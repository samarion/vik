#!/usr/bin/env python3
"""Differential fuzzer: VIK against z3 and cvc5 on random SMT-LIB scripts.

    fuzz.py run [--minutes M] [--seed S] [--jobs J] [--out DIR] [--classpath CP] [--lift N,...]
    fuzz.py show SEED INDEX [--lift N,...]          prints script INDEX of the run of seed SEED
    fuzz.py check FILE... [--classpath CP]          the comparison on the scripts given

A script declares random datatypes (Bool, Int, bit-vector, datatype, recursive and declared-sort fields, some
parametric instances) and constants, sometimes functions and arrays, sometimes a second family of datatypes
inside a level, and asserts random terms over them: check-sat, push, more assertions, check-sat, pop, check-sat,
each check followed by get-model. Script INDEX of seed SEED depends on the two and on this file only, so a run is
reproduced by its seed on the same commit (the number of scripts depends on the machine's speed).

Every check-sat is compared. WRONG: VIK answers sat or unsat, and z3 and cvc5 agree on the other answer.
BADMODEL: VIK answers sat and z3 finds the model it printed contradicts the declarations and assertions in scope
(each constant's value asserted, each function's definition in place of its declaration, the abstract values
distinct constants). CRASH: VIK throws. HUNG: VIK runs two seconds past its deadline. A check VIK leaves unknown,
or the oracles do not agree on, and a model z3 cannot read, are counted but are not findings.

`run` fuzzes for the given time, then minimizes the findings (the check-sat alone if it shows the failure, or else
the whole script; assertions dropped while the failure persists), writes DIR/report.md, the scripts under DIR/failures/ (and a few of each known shape under
DIR/known/), and exits with 1 when a finding is not a known shape (KNOWN). VIK runs through the harness
io.bovel.bench.vik.FuzzBatch, on the classpath `--classpath` gives or sbt prints (bench/runtimeClasspath); z3 and
cvc5 are those of bench/native/bin (bench/fetch-native.sh, pinned versions) or else of the PATH. Python's
standard library only.
"""
import argparse, collections, itertools, os, random, re, shutil, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if os.path.isdir(os.path.join(ROOT, "bench/native/bin")):
    os.environ["PATH"] = os.path.join(ROOT, "bench/native/bin") + os.pathsep + os.environ["PATH"]
SECONDS = 10  # every solver run holds to the ten-second budget of the benchmarks
BATCH = 20  # scripts per JVM
Z3 = ["z3", "-T:%d" % SECONDS, "-in"]
CVC5 = ["cvc5", "--tlimit=%d" % (SECONDS * 1000), "--incremental", "--lang=smt2"]

# Open issues whose shapes the fuzzer would otherwise find at every run, so that a finding is a new bug. Each
# is kept out of the scripts or its findings are reported under the issue, without failing the run. `--lift N`
# brings one back, to check a fix; once it is merged, delete the issue's line here and the code that reads it.
KNOWN = {
    125: "a Bool datatype field, or a field of a finite datatype under a datatype VIK counts as infinite: not "
         "generated (fixed by PR #128, not merged)",
    126: "a bit-vector datatype field of 1 to 3 bits: not generated, the fields are 4 or 8 bits wide",
    127: "BADMODEL on a script with a datatype VIK counts as infinite: reported under the issue",
    133: "arrays without an Int, Real or store term: a script with arrays gets an unrelated Int term",
    138: "BADMODEL whose model has an abstract bit-vector (an array index): reported under the issue",
    154: "an array of bit-vector elements: not generated",
}
# VIK counts a datatype as infinite when it is recursive or has an Int, declared-sort or bit-vector field below
# (has_infinite_datatype). Not generated either, and not liftable: datatype fields of an array sort (#153: finite
# ones are unbounded; #134, #135, #139 and #141 are open on array fields too). A model with a parametric
# constructor is printed by its internal name (#142), which z3 cannot read: such models are counted, not checked.


# ---- s-expressions

TOKEN = re.compile(r'\s+|;[^\n]*|(\()|(\))|(\|[^|]*\||"(?:[^"]|"")*"|[^\s()|";]+)')


def parse(text):
    """The s-expressions of a text, as nested lists of atoms (comments skipped)."""
    stack = [[]]
    for m in TOKEN.finditer(text):
        if m.group(1):
            stack.append([])
        elif m.group(2) and len(stack) > 1:
            done = stack.pop()
            stack[-1].append(done)
        elif m.group(3):
            stack[-1].append(m.group(3))
    return stack[0]


def show(x):
    return x if isinstance(x, str) else "(" + " ".join(map(show, x)) + ")"


def atoms(x):
    if isinstance(x, str):
        yield x
    else:
        for y in x:
            yield from atoms(y)


# ---- sorts

def datatype_defs(decls):
    """The datatypes declared: name -> (sort parameters, [(constructor, [(selector, sort)])]), sorts as parsed."""
    defs = {}
    def ctors(body):
        params = []
        if body and body[0] == "par":
            params, body = body[1], body[2]
        return params, [(c[0], [(f[0], f[1]) for f in c[1:]]) if isinstance(c, list) else (c, []) for c in body]
    for d in map(parse, decls):
        d = d[0]
        if d[0] == "declare-datatypes":
            for (name, _), body in zip(d[1], d[2]):
                defs[name] = ctors(body)
        elif d[0] == "declare-datatype":
            defs[d[1]] = ctors(d[2])
    return defs


def substitute(sort, sub):
    return sub.get(sort, sort) if isinstance(sort, str) else [substitute(s, sub) for s in sort]


def finite(sort, defs, bits=True, seen=()):
    """Whether a sort has finitely many values; a recursive datatype, Int, Real and declared sorts do not. With
    `bits` false, a bit-vector counts as infinite, as it does for VIK under a datatype (#126)."""
    if sort == "Bool" or (bits and isinstance(sort, list) and sort[:2] == ["_", "BitVec"]):
        return True
    if isinstance(sort, list) and sort[0] == "Array":
        return finite(sort[1], defs, bits, seen) and finite(sort[2], defs, bits, seen)
    name, args = (sort, []) if isinstance(sort, str) else (sort[0], sort[1:])
    if name not in defs or show(sort) in seen:
        return False
    params, ctors = defs[name]
    sub = dict(zip(params, args))
    return all(finite(substitute(t, sub), defs, bits, seen + (show(sort),)) for _, fields in ctors for _, t in fields)


def has_infinite_datatype(decls):
    """Whether a datatype sort of the declarations (a datatype, or one a constant or function names) is infinite
    for VIK: recursive, or with an Int, declared-sort or bit-vector field somewhere below."""
    defs = datatype_defs(decls)
    sorts = [name for name, (params, _) in defs.items() if not params]
    for d in map(parse, decls):
        d = d[0]
        if d[0] == "declare-const":
            sorts.append(d[2])
        elif d[0] == "declare-fun":
            sorts += d[2] + [d[3]]
    return any((s if isinstance(s, str) else s[0]) in defs and not finite(s, defs, bits=False) for s in sorts)


# ---- the generator

WIDTHS = [1, 2, 3, 4, 8]  # of bit-vector constants and terms


def bv(w):
    return "(_ BitVec %d)" % w


def bv_width(s):
    m = re.match(r"\(_ BitVec (\d+)\)$", s)
    return int(m.group(1)) if m else None


class Gen:
    """The declarations and terms of one script, from the script's random stream. `names` are the prefixes of
    datatypes, constructors, selectors and constants, so that a second family declared in a level is apart."""

    def __init__(self, r, lifted, names=("D", "c", "s", "k")):
        self.r, self.lifted, self.names = r, lifted, names
        self.dts = {}  # datatype sort (a name or a parametric instance) -> [(constructor, [(selector, sort)])]
        self.consts = {}  # sort -> constant names
        self.funs = []  # (name, argument sorts, result sort)
        self.arrays = []  # (array sort, index sort, element sort)
        self.decls = []
        self.uninterpreted = False
        self.field_widths = [1, 2, 3, 4, 8] if 126 in lifted else [4, 8]  # #126

    def finite(self, sort):
        """Whether VIK counts a sort as finite: a bit-vector field makes a datatype infinite (#126)."""
        defs = {d: ([], [(c, [(s, parse(t)[0]) for s, t in f]) for c, f in cs]) for d, cs in self.dts.items()}
        return finite(parse(sort)[0], defs, bits=False)

    def make_datatypes(self, uninterpreted=None, parametric=True):
        """Datatypes, mutually recursive in declaration order, the first constructor of each not recursive."""
        r, (D, C, S, _) = self.r, self.names
        if uninterpreted is None:
            uninterpreted = r.random() < 0.3
            if uninterpreted:
                self.decls.append("(declare-sort U 0)")
        self.uninterpreted = uninterpreted
        fw = self.field_widths
        base = ["Bool", "Int"] + [bv(w) for w in fw] + (["U"] if uninterpreted else [])
        names = ["%s%d" % (D, i) for i in range(r.randint(1, 3))]
        for i, d in enumerate(names):
            ctors = []
            for j in range(r.randint(1, 3)):
                fields = []
                for k in range(r.randint(0, 2) if j else r.randint(0, 1)):
                    s = r.choice(base + names[:i] + ([d] if j else []))
                    if r.random() < 0.35:  # towards small finite sorts
                        s = r.choice(["Bool", bv(fw[0]), bv(fw[1])] + names[:i])
                    fields.append(("%s%d_%d_%d" % (S, i, j, k), s))
                ctors.append(("%s%d_%d" % (C, i, j), fields))
            self.dts[d] = ctors
        if 125 not in self.lifted:
            # #125: on main a Bool field is unbounded, and so is a field of a finite datatype under an infinite one,
            # infinite as VIK counts it (a bit-vector field below makes it so). A bit-vector in place of the first,
            # an Int in place of the second: no datatype changes finiteness but those already infinite, so one pass
            # is enough.
            self.dts = {d: [(c, [(s, bv(fw[0]) if t == "Bool" else t) for s, t in fields]) for c, fields in cs]
                        for d, cs in self.dts.items()}
            for d in names:
                if not self.finite(d):
                    self.dts[d] = [(c, [(s, "Int" if t in self.dts and self.finite(t) else t) for s, t in fields])
                                   for c, fields in self.dts[d]]
        self.decls.append("(declare-datatypes (%s) (%s))" % (
            " ".join("(%s 0)" % d for d in names),
            " ".join("(%s)" % " ".join("(%s%s)" % (c, "".join(" (%s %s)" % f for f in fs)) for c, fs in self.dts[d])
                     for d in names)))
        if parametric and r.random() < 0.3:
            self.decls.append("(declare-datatype Opt (par (T) ((none) (some (val T)))))")
            self.decls.append("(declare-datatype Pair (par (A B) ((pair (fst A) (snd B)))))")
            for t in (bv(r.choice(fw)), r.choice(names)) + (("Bool",) if 125 in self.lifted else ()):
                self.dts["(Opt %s)" % t] = [("(as none (Opt %s))" % t, []), ("some", [("val", t)])]
            if 125 in self.lifted:
                a, b = r.choice(base), r.choice(names + ["Bool"])
            elif self.finite(b := r.choice(names)):  # #125: no Bool, and both finite or the second infinite
                a = r.choice([d for d in names if self.finite(d)])
            else:
                a = r.choice(["Int"] + [bv(w) for w in fw] + (["U"] if uninterpreted else []))
            self.dts["(Pair %s %s)" % (a, b)] = [("pair", [("fst", a), ("snd", b)])]

    def sorts(self):
        return ["Bool", "Int"] + [bv(w) for w in WIDTHS] + list(self.dts) + (["U"] if self.uninterpreted else [])

    def declare_consts(self):
        r, k = self.r, 0
        for s in self.sorts():
            n = r.randint(1, 4) if s in self.dts else r.randint(1, 2) if s == "U" else r.randint(0, 2)
            for _ in range(n):
                name = "%s%d" % (self.names[3], k)
                k += 1
                self.consts.setdefault(s, []).append(name)
                self.decls.append("(declare-const %s %s)" % (name, s))

    def declare_funs(self):
        """Uninterpreted functions, and array constants."""
        r = self.r
        ss = [s for s in self.sorts() if s != "U"]
        for i in range(r.randint(1, 3)):
            args, res = [r.choice(ss) for _ in range(r.randint(1, 2))], r.choice(ss)
            self.funs.append(("f%d" % i, args, res))
            self.decls.append("(declare-fun f%d (%s) %s)" % (i, " ".join(args), res))
        # #154: reads at an extensionality witness are unbounded for bit-vector elements.
        elements = ss if 154 in self.lifted else [s for s in ss if bv_width(s) is None]
        for i in range(r.randint(0, 2)):
            idx = r.choice([bv(r.choice([1, 2, 3])), "Int", r.choice([d for d in self.dts])])
            el = r.choice(elements)
            srt = "(Array %s %s)" % (idx, el)
            self.arrays.append((srt, idx, el))
            for j in range(r.randint(1, 2)):
                name = "a%d_%d" % (i, j)
                self.consts.setdefault(srt, []).append(name)
                self.decls.append("(declare-const %s %s)" % (name, srt))

    # ---- terms

    def lit(self, s):
        r = self.r
        if s == "Bool":
            return r.choice(["true", "false"])
        if s == "Int":
            v = r.randint(-3, 5)
            return str(v) if v >= 0 else "(- %d)" % -v
        w = bv_width(s)
        if w:
            return "#b" + format(r.randrange(1 << w), "0%db" % w)
        return None

    def term(self, s, depth):
        r, opts = self.r, []
        if self.consts.get(s):
            opts += [lambda: r.choice(self.consts[s])] * 3
        if self.lit(s) is not None:
            opts.append(lambda: self.lit(s))
        if depth > 0:
            sub = lambda t: self.term(t, depth - 1)
            for c, fields in self.dts.get(s, []):
                opts.append(lambda c=c, fields=fields: "(%s %s)" % (c, " ".join(sub(t) for _, t in fields))
                            if fields else c)
            for d, cs in self.dts.items():  # selectors into s
                for c, fields in cs:
                    for sel, t in fields:
                        if t == s:
                            opts.append(lambda sel=sel, d=d: "(%s %s)" % (sel, sub(d)))
            opts.append(lambda: "(ite %s %s %s)" % (sub("Bool"), sub(s), sub(s)))
            for f, args, res in self.funs:
                if res == s:
                    opts += [lambda f=f, args=args: "(%s %s)" % (f, " ".join(sub(t) for t in args))] * 2
            for srt, idx, el in self.arrays:
                if el == s:
                    opts += [lambda srt=srt, idx=idx: "(select %s %s)" % (sub(srt), sub(idx))] * 2
                if srt == s:
                    opts.append(lambda srt=srt, idx=idx, el=el: "(store %s %s %s)" % (sub(srt), sub(idx), sub(el)))
            w = bv_width(s)
            if w:
                opts += [lambda: "(%s %s %s)" % (r.choice(["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor"]),
                                                 sub(s), sub(s)),
                         lambda: "(%s %s)" % (r.choice(["bvneg", "bvnot"]), sub(s)),
                         lambda: "(%s %s #b%s)" % (r.choice(["bvshl", "bvlshr", "bvashr"]), sub(s),
                                                   format(r.randint(0, min(w + 1, (1 << w) - 1)), "0%db" % w)),
                         lambda: "(%s %s %s)" % (r.choice(["bvudiv", "bvurem"]), sub(s), self.lit(s))]
                if w < 8:
                    W = r.choice([x for x in WIDTHS if x > w])
                    j = r.randint(0, W - w)
                    opts.append(lambda: "((_ extract %d %d) %s)" % (j + w - 1, j, sub(bv(W))))
                small = [x for x in WIDTHS if x < w]
                if small:
                    v = r.choice(small)
                    if w - v in WIDTHS:
                        opts.append(lambda: "(concat %s %s)" % (sub(bv(v)), sub(bv(w - v))))
                    opts.append(lambda: "((_ %s %d) %s)" % (r.choice(["zero_extend", "sign_extend"]), w - v,
                                                            sub(bv(v))))
            if s == "Int":
                opts += [lambda: "(+ %s %s)" % (sub("Int"), sub("Int")),
                         lambda: "(- %s %s)" % (sub("Int"), sub("Int")),
                         lambda: "(* %s %s)" % (self.lit("Int"), sub("Int"))]
            if s == "Bool":
                opts += [lambda: "(not %s)" % sub("Bool"),
                         lambda: "(%s %s %s)" % (r.choice(["and", "or", "=>"]), sub("Bool"), sub("Bool"))]
                opts += [lambda: self.atom(depth)] * 3
        if not opts:  # no constant, no literal, no depth left: the first constructor, not recursive
            c, fields = self.dts[s][0]
            return "(%s %s)" % (c, " ".join(self.term(t, 0) for _, t in fields)) if fields else c
        return r.choice(opts)()

    def atom(self, depth):
        r = self.r
        s = r.choice(self.sorts() + [a for a, _, _ in self.arrays])
        k = r.random()
        if s in self.dts and not s.startswith("(") and k < 0.3:  # z3 4.14 finds a parametric tester ambiguous
            c = re.sub(r"\(as (\S+) .*", r"\1", r.choice(self.dts[s])[0])
            return "((_ is %s) %s)" % (c, self.term(s, depth - 1))
        if bv_width(s) and k < 0.5:
            return "(%s %s %s)" % (r.choice(["bvult", "bvule", "bvslt", "bvsle", "bvugt", "bvsge"]),
                                   self.term(s, depth - 1), self.term(s, depth - 1))
        if s == "Int" and k < 0.5:
            return "(%s %s %s)" % (r.choice(["<=", "<"]), self.term(s, depth - 1), self.term(s, depth - 1))
        if k < 0.75:
            return "(= %s %s)" % (self.term(s, depth - 1), self.term(s, depth - 1))
        return "(distinct %s)" % " ".join(self.term(s, depth - 1) for _ in range(r.randint(2, 4)))

    def assertion(self):
        return self.term("Bool", self.r.randint(1, 3))

    def pressure(self):
        """A `distinct` over the constants of a datatype sort, and testers on them: cardinality pressure."""
        r = self.r
        ds = [d for d in self.dts if len(self.consts.get(d, [])) >= 2]
        if not ds:
            return []
        d = r.choice(ds)
        c = re.sub(r"\(as (\S+) .*", r"\1", r.choice(self.dts[d])[0])
        return ["(distinct %s)" % " ".join(self.consts[d])] + \
            ["((_ is %s) %s)" % (c, k) for k in self.consts[d] if r.random() < 0.7 and not d.startswith("(")]


def generate(seed, index, lifted=frozenset()):
    """Script `index` of the run of `seed`: plain, with functions and arrays, or with datatypes declared in a level."""
    r = random.Random(seed * 1000000 + index)
    variant = r.choice(["plain", "plain", "funs", "funs", "levels"])
    g = Gen(r, lifted)
    g.make_datatypes()
    g.declare_consts()
    lines = ["; bench/fuzz.py show %d %d (%s)" % (seed, index, variant),
             "(set-logic ALL)", "(set-option :produce-models true)"]
    asserts = lambda gen, lo, hi, p: [gen.assertion() for _ in range(r.randint(lo, hi))] + \
        (gen.pressure() if r.random() < p else [])
    if variant == "levels":
        h = Gen(r, lifted, names=("E", "e", "t", "j"))
        h.make_datatypes(uninterpreted=g.uninterpreted, parametric=False)
        h.declare_consts()
        for s, names in g.consts.items():  # the outer constants of the sorts both know
            if s not in g.dts:
                h.consts.setdefault(s, []).extend(names)
        base, inner, after = asserts(g, 1, 3, 0.5), asserts(h, 1, 3, 0.5), asserts(g, 1, 2, 0)
        lines += g.decls + ["(assert %s)" % a for a in base] + ["(check-sat)", "(get-model)", "(push 1)"]
        lines += h.decls + ["(assert %s)" % a for a in inner] + ["(check-sat)", "(get-model)", "(pop 1)"]
        lines += ["(assert %s)" % a for a in after] + ["(check-sat)", "(get-model)"]
    else:
        if variant == "funs":
            g.declare_funs()
        base = asserts(g, 1, 4, 0.6)
        if g.arrays and 133 not in lifted:
            # #133: extensionality is skipped without an Int, Real or store term; this one turns it on. The minimizer
            # keeps it (PROTECTED).
            g.decls.append("(declare-fun issue133 (Int) Int)")
            base.append("(= (issue133 0) 1)")
        inner = asserts(g, 1, 3, 0.3)
        lines += g.decls + ["(assert %s)" % a for a in base] + ["(check-sat)", "(get-model)", "(push 1)"]
        lines += ["(assert %s)" % a for a in inner] + ["(check-sat)", "(get-model)", "(pop 1)", "(check-sat)",
                                                       "(get-model)"]
    return "\n".join(lines) + "\n"


PROTECTED = re.compile(r"\bissue\d+\b")  # what the minimizer keeps: the terms that keep a known shape away


# ---- the scripts' check-sats

DECLARATIONS = ("declare-sort", "define-sort", "declare-datatype", "declare-datatypes", "declare-const",
                "declare-fun", "define-fun")


def checks(text):
    """For each check-sat of a script: the declarations and the assertions in scope, and whether a get-model
    follows it."""
    levels, out = [([], [])], []
    for c in parse(text):
        head = c[0] if isinstance(c, list) and c and isinstance(c[0], str) else None
        if head in DECLARATIONS:
            levels[-1][0].append(show(c))
        elif head == "assert":
            levels[-1][1].append(show(c[1]))
        elif head == "push":
            levels += [([], []) for _ in range(int(c[1]) if len(c) > 1 else 1)]
        elif head == "pop":
            del levels[len(levels) - (int(c[1]) if len(c) > 1 else 1):]
        elif head == "check-sat":
            out.append({"decls": [d for l in levels for d in l[0]], "asserts": [a for l in levels for a in l[1]],
                        "model": False})
        elif head == "get-model" and out:
            out[-1]["model"] = True
    return out


def standalone(check, model):
    return "\n".join(["(set-logic ALL)", "(set-option :produce-models true)"] + check["decls"] +
                     ["(assert %s)" % a for a in check["asserts"]] + ["(check-sat)"] +
                     (["(get-model)"] if model else [])) + "\n"


# ---- the solvers

def vik(classpath, paths, seconds=SECONDS):
    """VIK's responses to each script, through the harness: path -> lines."""
    try:
        out = subprocess.run(["java", "-Xmx2g", "-cp", classpath, "io.bovel.bench.vik.FuzzBatch", str(seconds)] +
                             paths, capture_output=True, text=True, timeout=len(paths) * (seconds + 3) + 60).stdout
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
    res, cur = {}, None
    for line in out.splitlines():
        if line.startswith("=== "):
            cur = line[4:]
            res[cur] = []
        elif cur:
            res[cur].append(line)
    return res


def oracle(cmd, text, count):
    """An oracle's answers to the check-sats of a script, or None when it errs or does not answer each."""
    q = "".join(l + "\n" for l in text.splitlines() if l.strip() not in ("(get-model)",))
    try:
        out = subprocess.run(cmd, input=q, capture_output=True, text=True, timeout=SECONDS * 2 + 10).stdout
    except subprocess.TimeoutExpired:
        return None
    lines = [l.strip() for l in out.splitlines()]
    answers = [l for l in lines if l in ("sat", "unsat", "unknown")]
    if any(l.startswith("(error") for l in lines) or len(answers) != count:
        return None
    return answers


def responses(lines):
    """VIK's answers, each with the model printed after it (or None)."""
    out = []
    for i, l in enumerate(lines):
        if l in ("sat", "unsat", "unknown"):
            nxt = lines[i + 1] if i + 1 < len(lines) else ""
            out.append((l, nxt if nxt.startswith("(") and not nxt.startswith(("(error", "(crash", "(hung")) else None))
    return out


ABSTRACT = re.compile(r"^\|?@(.*)!(\d+)\|?$")


def model_check(check, model):
    """z3's verdict on VIK's model at a check-sat: 'sat', 'unsat', or 'error' (z3 refused the query)."""
    defs = [d for d in parse(model)[0] if isinstance(d, list) and d[:1] == ["define-fun"]] if parse(model) else []
    abstract = {}  # an abstract value -> (constant, sort)
    for a in atoms(defs):
        m = ABSTRACT.match(a)
        if m and a not in abstract:
            abstract[a] = ("abstract%d" % len(abstract), m.group(1))
    fix = lambda x: abstract[x][0] if isinstance(x, str) and x in abstract else x if isinstance(x, str) else \
        [fix(y) for y in x]
    funs = {d[1]: d for d in defs if d[2]}
    consts = {d[1]: d for d in defs if not d[2]}
    decls, declared = [], set()
    for d in check["decls"]:
        p = parse(d)[0]
        if p[0] in ("declare-fun", "declare-const"):
            declared.add(p[1])
            if p[1] in funs:
                continue  # defined below instead
        decls.append(d)
    last_sort = max([i for i, d in enumerate(decls) if d.startswith(("(declare-sort", "(declare-datatype"))],
                    default=-1)
    by_sort = collections.defaultdict(list)
    for c, s in abstract.values():
        by_sort[s].append(c)
    extra = ["(declare-const %s %s)" % (c, s) for c, s in abstract.values()] + \
        ["(assert (distinct %s))" % " ".join(cs) for cs in by_sort.values() if len(cs) > 1] + \
        [show(fix(d)) for d in funs.values()]
    q = decls[:last_sort + 1] + extra + decls[last_sort + 1:] + ["(assert %s)" % a for a in check["asserts"]] + \
        ["(assert (= %s %s))" % (c, show(fix(d[4]))) for c, d in consts.items() if c in declared] + ["(check-sat)"]
    try:
        out = subprocess.run(Z3, input="(set-logic ALL)\n" + "\n".join(q) + "\n", capture_output=True, text=True,
                             timeout=SECONDS * 2).stdout.split()
    except subprocess.TimeoutExpired:
        return "error"
    return "error" if not out or "(error" in out else out[-1]


# ---- the comparison

def known(kind, check, model, lifted):
    """The open issue a finding is a shape of, or None."""
    if kind == "BADMODEL" and 127 not in lifted and has_infinite_datatype(check["decls"]):
        return 127
    if kind == "BADMODEL" and 138 not in lifted and re.search(r"@\(_ BitVec", model or ""):
        return 138
    return None


def compare(text, lines, lifted, stats):
    """The findings on one script, given VIK's responses: [(kind, check index, detail, known issue)]."""
    cs = checks(text)
    stats["scripts"] += 1
    if lines == ["(hung)"] or (lines and lines[-1] == "(hung)"):
        return [("HUNG", None, "no answer two seconds past the %d-second deadline" % SECONDS, None)]
    bad = [l for l in lines if l.startswith(("(crash", "(error")) and l != '(error "no model")']
    if bad:
        if re.search(r"[Uu]nsupported|not supported", " ".join(bad)):
            stats["refused by VIK"] += 1
            return []
        return [("CRASH", None, bad[0][:300], None)]
    got = responses(lines)
    if len(got) != len(cs):
        return [("CRASH", None, "%d answers to %d check-sats" % (len(got), len(cs)), None)]
    z3, cvc5 = oracle(Z3, text, len(cs)), oracle(CVC5, text, len(cs))
    findings = []
    for k, ((a, model), check) in enumerate(zip(got, cs)):
        stats["check-sats"] += 1
        z, c = (z3 or ["?"] * len(cs))[k], (cvc5 or ["?"] * len(cs))[k]
        if a == "unknown":
            stats["unknown (VIK)"] += 1
        elif z in ("sat", "unsat") and z == c:
            if a != z:
                findings.append(("WRONG", k, "VIK %s, z3 and cvc5 %s" % (a, z), None))
                continue
            stats["agreed"] += 1
        else:
            stats["no verdict (z3 %s, cvc5 %s)" % (z, c)] += 1
        if a == "sat" and check["model"] and model is not None:
            v = model_check(check, model)
            if v == "unsat":
                findings.append(("BADMODEL", k, "z3 finds VIK's model contradicts the script",
                                 known("BADMODEL", check, model, lifted)))
            elif v == "error":  # #142: parametric constructors print by their internal names, `|some@Int|`
                stats["models z3 refused" + (" (#142)" if re.search(r"[^\s()|]@", model) else "")] += 1
    return findings


def signature(finding):
    """What a smaller script must show to count as the same failure: the kind, the check-sat, and for a crash the
    exception and its message without the names and numbers."""
    kind, k, detail = finding[:3]
    return kind, k, re.sub(r"\S*\d\S*", "#", detail) if kind == "CRASH" else ""


def shrink(commands, still, stop):
    """Assertions dropped one at a time while `still` holds, then the constants and functions nothing uses."""
    changed = True
    while changed and time.time() < stop:
        changed = False
        for i, c in enumerate(commands):
            if c.startswith("(assert") and not PROTECTED.search(c) and still(commands[:i] + commands[i + 1:]):
                commands, changed = commands[:i] + commands[i + 1:], True
                break
            if time.time() > stop:
                break
    used = set(atoms(parse(" ".join(c for c in commands if not c.startswith("(declare")))))
    name = lambda c: re.match(r"\(declare-(?:const|fun) (\S+)", c)
    trial = [c for c in commands if not name(c) or name(c).group(1) in used]
    return trial if trial != commands and still(trial) else commands


def minimize(finding, text, classpath, lifted, work, budget):
    """A smaller script with the same failure: the check-sat alone if it shows it, or else the whole script, with
    assertions dropped while the failure persists; None when neither shows it (or the finding is a hang)."""
    kind, k = finding[:2]
    if kind == "HUNG":
        return None
    stop = time.time() + budget
    path = os.path.join(work, "min-%d.smt2" % threading.get_ident())

    def shows(commands, target):
        text = "\n".join(commands) + "\n"
        with open(path, "w") as f:
            f.write(text)
        found = compare(text, vik(classpath, [path]).get(path, []), lifted, collections.Counter())
        return any(f[3] is None and signature(f) == target for f in found)

    tries = []
    if k is not None:
        alone = checks(text)[k]
        tries.append(([show(c) for c in parse(standalone(alone, kind == "BADMODEL"))], (kind, 0, "")))
    tries.append(([show(c) for c in parse(text)], signature(finding)))
    for commands, target in tries:
        if shows(commands, target):
            return "\n".join(shrink(commands, lambda c: shows(c, target), stop)) + "\n"
    return None


# ---- the commands

def classpath(given):
    if given:
        return given
    print("asking sbt for bench/runtimeClasspath (it compiles VIK and the harness first)", flush=True)
    out = subprocess.run(["sbt", "--server", "--no-colors", "print bench/runtimeClasspath"], cwd=ROOT,
                         capture_output=True, text=True).stdout
    cp = [l for l in out.splitlines() if l.startswith("/")]
    if not cp:
        sys.exit("sbt printed no bench/runtimeClasspath:\n" + out[-2000:])
    return cp[-1]


def canary(cp, work):
    path = os.path.join(work, "canary.smt2")
    with open(path, "w") as f:
        f.write("(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n")
    got = vik(cp, [path]).get(path)
    if got != ["sat"]:
        sys.exit("the harness does not run on this classpath (%r): bench/runtimeClasspath, built?" % got)
    for cmd in (Z3, CVC5):
        if not shutil.which(cmd[0]):
            sys.exit("no %s on the PATH: bench/fetch-native.sh puts the pinned one in bench/native/bin" % cmd[0])


def git(*args):
    try:
        return subprocess.run(["git"] + list(args), cwd=ROOT, capture_output=True, text=True).stdout.strip()
    except OSError:
        return "?"


def version(cmd):
    out = subprocess.run([cmd, "--version"], capture_output=True, text=True).stdout.splitlines()
    return out[0] if out else "?"


def run(args):
    lifted = frozenset(args.lift)
    seed = args.seed if args.seed is not None else int(time.strftime("%Y%m%d", time.gmtime()))
    out = os.path.abspath(args.out)
    work = os.path.join(out, "work")
    shutil.rmtree(out, ignore_errors=True)
    for d in ("work", "failures", "known"):
        os.makedirs(os.path.join(out, d))
    cp = classpath(args.classpath)
    canary(cp, work)
    commit = git("rev-parse", "--short", "HEAD")
    print("seed %d, commit %s, %g minutes, %d jobs%s; one script: bench/fuzz.py show %d <index>" % (
        seed, commit, args.minutes, args.jobs, ", lifted %s" % sorted(lifted) if lifted else "", seed), flush=True)
    start = time.time()
    deadline = start + args.minutes * 60
    batches, lock = itertools.count(), threading.Lock()
    stats, findings = collections.Counter(), []  # findings: (kind, k, detail, issue, index, text)

    def worker():
        while time.time() < deadline:
            with lock:
                b = next(batches)
            texts = {i: generate(seed, i, lifted) for i in range(b * BATCH, (b + 1) * BATCH)}
            paths = {i: os.path.join(work, "%d.smt2" % i) for i in texts}
            for i, p in paths.items():
                with open(p, "w") as f:
                    f.write(texts[i])
            answers, pending = {}, list(paths.values())
            while pending:  # the scripts after one that took the JVM down run again, in a JVM of their own
                answers.update(vik(cp, pending))
                missing = [p for p in pending if p not in answers]
                pending = missing if len(missing) < len(pending) else []
            local = collections.Counter()
            for i, p in paths.items():
                for f in compare(texts[i], answers.get(p, []), lifted, local):
                    with lock:
                        findings.append(f + (i, texts[i]))
                os.unlink(p)
            with lock:
                stats.update(local)
                if stats["scripts"] // 500 != (stats["scripts"] - local["scripts"]) // 500:
                    print("%4.0f s: %d scripts, %d findings" % (time.time() - start, stats["scripts"],
                                                                 len(findings)), flush=True)

    with ThreadPoolExecutor(args.jobs) as ex:
        for f in [ex.submit(worker) for _ in range(args.jobs)]:
            f.result()
    elapsed = time.time() - start
    findings.sort(key=lambda f: (f[4], f[1] if f[1] is not None else -1))
    new = [f for f in findings if f[3] is None]
    print("%d scripts in %.0f s: %d findings, %d of a known shape; minimizing" % (
        stats["scripts"], elapsed, len(findings), len(findings) - len(new)), flush=True)

    def name(f):
        return "s%d-%d%s-%s" % (seed, f[4], "" if f[1] is None else "-check%d" % f[1], f[0].lower())

    def header(f):
        return "; %s at %s: %s\n; on %s, seed %d, script %d (bench/fuzz.py show %d %d)\n" % (
            f[0], "the script" if f[1] is None else "check-sat %d" % (f[1] + 1), f[2], commit, seed, f[4], seed, f[4])

    minimized = {}
    to_minimize = new[:args.minimize]
    with ThreadPoolExecutor(args.jobs) as ex:
        for f, m in zip(to_minimize, ex.map(lambda f: minimize(f, f[5], cp, lifted, work, 120),
                                            to_minimize)):
            minimized[name(f)] = m
    for f in new:
        with open(os.path.join(out, "failures", name(f) + ".smt2"), "w") as fh:
            fh.write(header(f) + f[5])
        if minimized.get(name(f)):
            with open(os.path.join(out, "failures", name(f) + ".min.smt2"), "w") as fh:
                fh.write(header(f) + minimized[name(f)])
    per_issue = collections.defaultdict(list)
    for f in findings:
        if f[3] is not None:
            per_issue[f[3]].append(f)
    for issue, fs in per_issue.items():
        for f in fs[:3]:
            with open(os.path.join(out, "known", "issue%d-%s.smt2" % (issue, name(f))), "w") as fh:
                fh.write(header(f) + f[5])
    shutil.rmtree(work, ignore_errors=True)

    report = ["# Differential fuzzing of VIK", "",
              "Seed **%d** on `%s`, %.1f minutes on %d jobs: %d scripts, %d check-sats; z3 `%s`, cvc5 `%s`." % (
                  seed, commit, elapsed / 60, args.jobs, stats["scripts"], stats["check-sats"], version("z3"),
                  version("cvc5")),
              "Reproduce: `bench/fuzz.py run --seed %d --minutes %g%s` on this commit (CONTRIBUTING.md, "
              "\"Fuzzing\"), or `bench/fuzz.py check <file>` on a script of `failures/`." % (
                  seed, args.minutes, " --lift " + ",".join(map(str, sorted(lifted))) if lifted else ""), ""]
    if lifted:
        report += ["Lifted: %s." % ", ".join("#%d" % n for n in sorted(lifted)), ""]
    report += ["## %d new findings" % len(new), ""]
    if new:
        report += ["| Finding | Script | Check-sat | What | Minimized |", "|---|---|---|---|---|"]
        for f in new[:50]:
            report.append("| %s | `%s.smt2` | %s | %s | %s |" % (
                f[0], name(f), "" if f[1] is None else f[1] + 1, f[2].replace("|", "\\|"),
                "`%s.min.smt2`" % name(f) if minimized.get(name(f)) else "no"))
        report += ["", "And %d more, in `failures/`." % (len(new) - 50)] if len(new) > 50 else []
        report.append("")
    report += ["## Known shapes", "", "| Issue | Kept away by | Findings |", "|---|---|---|"]
    for n, what in KNOWN.items():
        report.append("| #%d | %s | %s |" % (n, "lifted" if n in lifted else what, len(per_issue.get(n, []))))
    report += ["", "## Counts", "", "| | |", "|---|---|"]
    report += ["| %s | %d |" % kv for kv in sorted(stats.items())]
    text = "\n".join(report) + "\n"
    with open(os.path.join(out, "report.md"), "w") as f:
        f.write(text)
    print(text)
    return 1 if new else 0


def check(args):
    lifted = frozenset(args.lift)
    work = os.path.abspath(args.out)
    os.makedirs(work, exist_ok=True)
    cp = classpath(args.classpath)
    canary(cp, work)
    paths = [os.path.abspath(p) for p in args.files]
    answers = vik(cp, paths)
    status = 0
    for p in paths:
        text = open(p).read()
        stats = collections.Counter()
        fs = compare(text, answers.get(p, []), lifted, stats)
        print("%s: %s" % (p, "; ".join("%s at %s: %s%s" % (
            f[0], "the script" if f[1] is None else "check-sat %d" % (f[1] + 1), f[2],
            " (#%d)" % f[3] if f[3] else "") for f in fs) or "no finding (%s)" % ", ".join(
            "%s %d" % kv for kv in sorted(stats.items()))))
        status |= any(f[3] is None for f in fs)
    return status


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = p.add_subparsers(dest="command", required=True)
    lift = lambda q: q.add_argument("--lift", type=lambda s: [int(x) for x in s.split(",") if x], default=[],
                                    help="issues whose shapes to generate and report again, e.g. 125,126")
    r = sub.add_parser("run", help="fuzz for a time, minimize, report")
    r.add_argument("--minutes", type=float, default=5)
    r.add_argument("--seed", type=int, help="default: today's date, YYYYMMDD (UTC)")
    r.add_argument("--jobs", type=int, default=min(os.cpu_count() or 1, 8))
    r.add_argument("--out", default=os.path.join(ROOT, "target/fuzz"))
    r.add_argument("--classpath", help="default: what sbt prints for bench/runtimeClasspath")
    r.add_argument("--minimize", type=int, default=10, help="how many new findings to minimize")
    lift(r)
    s = sub.add_parser("show", help="print one script of a run")
    s.add_argument("seed", type=int)
    s.add_argument("index", type=int)
    lift(s)
    c = sub.add_parser("check", help="compare VIK with z3 and cvc5 on the scripts given")
    c.add_argument("files", nargs="+")
    c.add_argument("--classpath")
    c.add_argument("--out", default=os.path.join(ROOT, "target/fuzz-check"))
    lift(c)
    args = p.parse_args()
    if args.command == "show":
        sys.stdout.write(generate(args.seed, args.index, frozenset(args.lift)))
        return 0
    return run(args) if args.command == "run" else check(args)


if __name__ == "__main__":
    sys.exit(main())
