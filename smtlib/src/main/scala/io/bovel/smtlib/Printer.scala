package io.bovel.smtlib

/** Prints scripts, formulas and terms back to SMT-LIB 2 text (one command per
 *  line), faithfully: the tree holds the script as written, so what comes out
 *  is what went in — up to normalized literals (`#xFF` prints as `(_ bv255 8)`)
 *  and `declare-const`, which prints as a `declare-fun`.
 */
object Printer:
  /** A symbol as SMT-LIB writes it: quoted when it holds a character a simple
   *  symbol cannot (the instances of polymorphic symbols at applied sorts,
   *  `cons@(List Int)`); an indexed identifier `(_ is c)` as it is.
   */
  def symbol(name: String): String =
    if name.startsWith("(_ ") || name.startsWith("(as ") then name
    else sexpr.SExpr.SSymbol(name).toString

  def print(script: Script): String = script.commands.map(print).mkString("", "\n", "\n")

  def print(command: Command): String = command match
    case Command.SetLogic(logic) => s"(set-logic $logic)"
    case Command.SetInfo(key, value) => s"(set-info $key $value)"
    case Command.DeclareSort(name, arity) => s"(declare-sort $name $arity)"
    case Command.DeclareFun(name, argSorts, sort) =>
      s"(declare-fun $name (${argSorts.map(_.text).mkString(" ")}) ${sort.text})"
    case Command.DeclareDatatypes(datatypes) =>
      val sorts = datatypes.map(d => s"(${d.name} 0)").mkString(" ")
      val declarations = datatypes.map { d =>
        d.constructors.map { c =>
          if c.selectors.isEmpty then s"(${c.name})"
          else s"(${c.name} ${c.selectors.map((s, sort) => s"($s ${sort.text})").mkString(" ")})"
        }.mkString("(", " ", ")")
      }.mkString(" ")
      s"(declare-datatypes ($sorts) ($declarations))"
    case Command.DefineFun(name, params, sort, body) =>
      val printed = body match
        case t: Term => print(t)
        case f: Formula => print(f)
      s"(define-fun $name (${params.map((p, s) => s"($p ${s.text})").mkString(" ")}) ${sort.text} $printed)"
    case Command.Assert(formula) => s"(assert ${print(formula)})"
    case Command.AssertNamed(name, formula) => s"(assert (! ${print(formula)} :named $name))"
    case Command.CheckSat => "(check-sat)"
    case Command.GetUnsatCore => "(get-unsat-core)"
    case Command.GetAssertions => "(get-assertions)"
    case Command.CheckSatAssuming(assumptions) => assumptions.map(print).mkString("(check-sat-assuming (", " ", "))")
    case Command.ResetAssertions => "(reset-assertions)"
    case Command.Reset => "(reset)"
    case Command.Push(n) => s"(push $n)"
    case Command.Pop(n) => s"(pop $n)"
    case Command.GetModel => "(get-model)"
    case Command.GetValue(items) => items.map(_._1).mkString("(get-value (", " ", "))")
    case Command.Exit => "(exit)"
    case Command.SetOption(key, value) => s"(set-option $key $value)"
    case Command.GetInfo(key) => s"(get-info $key)"
    case Command.Other(sexpr) => sexpr.toString

  private def bindings(bs: List[(String, Term | Formula)]): String =
    bs.map((name, value) =>
      value match
        case t: Term => s"($name ${print(t)})"
        case f: Formula => s"($name ${print(f)})"
    ).mkString(" ")

  def print(formula: Formula): String = formula match
    case Formula.True => "true"
    case Formula.False => "false"
    case Formula.Not(arg) => s"(not ${print(arg)})"
    case Formula.And(Nil) => "true"
    case Formula.And(args) => args.map(print).mkString("(and ", " ", ")")
    case Formula.Or(Nil) => "false"
    case Formula.Or(args) => args.map(print).mkString("(or ", " ", ")")
    case Formula.Implies(args) => args.map(print).mkString("(=> ", " ", ")")
    case Formula.Xor(args) => args.map(print).mkString("(xor ", " ", ")")
    case Formula.Iff(args) => args.map(print).mkString("(= ", " ", ")")
    case Formula.Eq(args) => args.map(print).mkString("(= ", " ", ")")
    case Formula.Distinct(args) => args.map(print).mkString("(distinct ", " ", ")")
    case Formula.Cmp(op, args) => args.map(print).mkString(s"(${op.name} ", " ", ")")
    case Formula.BvCmp(op, lhs, rhs) => s"(${op.name} ${print(lhs)} ${print(rhs)})"
    case Formula.Ite(cond, thn, els) => s"(ite ${print(cond)} ${print(thn)} ${print(els)})"
    case Formula.IsConstructor(constructor, arg) => s"((_ is $constructor) ${print(arg)})"
    case Formula.IsInt(arg) => s"(is_int ${print(arg)})"
    case Formula.Let(bs, body) => s"(let (${bindings(bs)}) ${print(body)})"
    case Formula.Pred(term) => print(term)

  def print(term: Term): String = term match
    case Term.Const(name) => symbol(name)
    case Term.Numeral(value) => if value.signum < 0 then s"(- ${-value})" else value.toString
    case Term.Decimal(unscaled, scale) =>
      val digits = unscaled.toString.reverse.padTo(scale + 1, '0').reverse
      s"${digits.dropRight(scale)}.${digits.takeRight(scale)}"
    case Term.Bits(value, width) => s"(_ bv$value $width)"
    case Term.App(fun, args) => args.map(print).mkString(s"(${print(fun)} ", " ", ")")
    case Term.ArithApp(op, args) => args.map(print).mkString(s"(${op.name} ", " ", ")")
    case Term.BvApp(op, args) =>
      val head = if op.indices.isEmpty then op.name else s"(_ ${op.name} ${op.indices.mkString(" ")})"
      args.map(print).mkString(s"($head ", " ", ")")
    case Term.Select(array, index) => s"(select ${print(array)} ${print(index)})"
    case Term.Store(array, index, value) => s"(store ${print(array)} ${print(index)} ${print(value)})"
    case Term.ConstArray(sort, value) => s"((as const ${sort.text}) ${print(value)})"
    case Term.Ite(cond, thn, els) => s"(ite ${print(cond)} ${print(thn)} ${print(els)})"
    case Term.Let(bs, body) => s"(let (${bindings(bs)}) ${print(body)})"
    case Term.Bool(formula) => print(formula)
