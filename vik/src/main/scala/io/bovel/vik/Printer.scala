package io.bovel.vik

import io.bovel.smtlib.Datatype

/** Prints lowered scripts, formulas and terms back to SMT-LIB 2 text (one
 *  command per line), e.g. to hand the problem the solver plays to another
 *  solver, or to show it (`io.bovel.vik.lower`, `get-assertions`, the models).
 *  One command is not SMT-LIB's: `(assert-global F)`, an assertion below every
 *  level ([[Command.AssertGlobal]]), which the standard has no way to write.
 */
object Printer:
  /** A symbol as SMT-LIB writes it: quoted when it holds a character a simple
   *  symbol cannot (the instances of polymorphic symbols at applied sorts,
   *  `cons@(List Int)`); an indexed identifier `(_ is c)` as it is.
   */
  def symbol(name: String): String =
    if name.startsWith("(_ is ") then
      s"(_ is ${symbol(name.stripPrefix("(_ is ").stripSuffix(")"))})" // its constructor quoted
    else if name.startsWith("(_ ") || name.startsWith("(as ") || name.startsWith("|") then name
    else if name.exists(c => c == ' ' || c == '(' || c == ')') then s"|$name|"
    else name

  def print(script: Script): String = script.commands.map(print).mkString("", "\n", "\n")

  def print(command: Command): String = command match
    case Command.SetLogic(logic) => s"(set-logic $logic)"
    case Command.SetInfo(key, value) => s"(set-info $key $value)"
    case Command.DeclareSort(name, arity) => s"(declare-sort ${symbol(name)} $arity)"
    case Command.DeclareFun(name, argSorts, sort) =>
      s"(declare-fun ${symbol(name)} (${argSorts.mkString(" ")}) $sort)"
    case Command.DeclareDatatypes(datatypes) => // every name as the script would write it (issue 33)
      val sorts = datatypes.map(d => s"(${symbol(d.name)} 0)").mkString(" ")
      val declarations = datatypes.map { d =>
        d.constructors.map { c =>
          if c.selectors.isEmpty then s"(${symbol(c.name)})"
          else s"(${symbol(c.name)} ${c.selectors.map((s, sort) => s"(${symbol(s)} $sort)").mkString(" ")})"
        }.mkString("(", " ", ")")
      }.mkString(" ")
      s"(declare-datatypes ($sorts) ($declarations))"
    case Command.Assert(formula) => s"(assert ${print(formula)})"
    case Command.AssertGlobal(formula) => s"(assert-global ${print(formula)})" // VIK's own: see the command
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
    case Command.GetValue(items, _) => items.map(_._1).mkString("(get-value (", " ", "))")
    case Command.Exit => "(exit)"
    case Command.SetOption(key, value) => s"(set-option $key $value)"
    case Command.GetInfo(key) => s"(get-info $key)"
    case Command.Other(sexpr) => sexpr.toString

  def print(formula: Formula): String = formula match
    case Formula.True => "true"
    case Formula.False => "false"
    case Formula.Not(arg) => s"(not ${print(arg)})"
    case Formula.And(Nil) => "true"
    case Formula.And(args) => args.map(print).mkString("(and ", " ", ")")
    case Formula.Or(Nil) => "false"
    case Formula.Or(args) => args.map(print).mkString("(or ", " ", ")")
    case Formula.Implies(lhs, rhs) => s"(=> ${print(lhs)} ${print(rhs)})"
    case Formula.Iff(lhs, rhs) => s"(= ${print(lhs)} ${print(rhs)})"
    case Formula.Ite(cond, thn, els) => s"(ite ${print(cond)} ${print(thn)} ${print(els)})"
    case Formula.Eq(lhs, rhs) => s"(= ${print(lhs)} ${print(rhs)})"
    case Formula.Pred(term) => print(term)
    case Formula.Le(lhs, rhs) => s"(<= ${print(lhs)} ${print(rhs)})"
    case Formula.Less(lhs, rhs) => s"(< ${print(lhs)} ${print(rhs)})"

  def print(term: Term): String = term match
    case Term.Const(name) => symbol(name)
    case Term.App(fun, args) => args.map(print).mkString(s"(${print(fun)} ", " ", ")")
    case Term.Num(value) => if value.signum < 0 then s"(- ${-value})" else value.toString
    case Term.Bool(formula) => print(formula)
    case Term.Linear(terms, constant) =>
      val summands = terms.map((a, t) => if a == 1 then print(t) else s"(* ${print(Term.Num(a))} ${print(t)})") ++
        Option.when(constant.signum != 0)(print(Term.Num(constant)))
      summands match
        case single :: Nil => single
        case _ => summands.mkString("(+ ", " ", ")")
