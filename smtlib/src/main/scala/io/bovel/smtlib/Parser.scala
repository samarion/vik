package io.bovel.smtlib

import scala.collection.mutable.HashMap

import io.bovel.smtlib.sexpr.{SExpr, SExprParser}
import io.bovel.smtlib.sexpr.SExpr.{SBits, SDecimal, SKeyword, SList, SNumeral, SString, SSymbol}

/** Reads an SMT-LIB 2 script (QF_UF, QF_LIA, QF_AX, the bit-vectors and VIK's
 *  into a [[Script]], as written: terms of uninterpreted, numeric and
 *  bit-vector sorts become [[Term]]s, Boolean ones [[Formula]]s, and nothing is
 *  rewritten — `let` keeps its names, `(= a b c)` stays chained, `(+ a b c)`
 *  n-ary. The solver's `Lowering` compiles the result. The parser's own work is
 *  reading and sorts: sorts of declared and bound symbols decide which tree a
 *  subterm belongs to (`=` on Booleans is equivalence, a Boolean application a
 *  [[Formula.Pred]]) and reject what no theory here speaks (strings, floats,
 *  ...). An unknown symbol is an error, and so is an ill-sorted term
 *  ([[SortCheck]]).
 */
/** One parser: it carries the declarations and macros the commands build up, so
 *  the next `parse` reads its input in their scope ([[Parser.parse]] makes a
 *  fresh one per input; a `vik.Session` keeps one).
 */
final class Parser:
  import Formula.*

  /** The declared symbols (functions with their whole function sort) and the
   *  macros of `define-fun`, with parameters, result sort and typed body.
   */
  private val functions = HashMap.empty[String, Sort]
  private val macros = HashMap.empty[String, (List[(String, Sort)], Sort, Term | Formula)]
  private val constructors = HashMap.empty[String, Constructor] // by name, for the patterns of `match`
  private var matches = 0 // the `match` scrutinees bound so far, for their names
  private val datatypeOf = HashMap.empty[String, String] // a constructor to its datatype, for the patterns
  private val instanceSymbols = scala.collection.mutable.HashSet.empty[String] // the symbols of instances
  private val sortCheck = SortCheck(functions, macros)

  /** Polymorphism, compiled away here: a sort parameter
   *  (`declare-sort-parameter`, or the `par` of a datatype) makes a rank
   *  polymorphic, and every use of the symbol at a monomorphic instance — the
   *  parameters bound by unification with the arguments' sorts, or named with
   *  `(as f τ)` — is a use of a monomorphic symbol `f@τ1@…`, declared on demand
   *  ([[instance]]) ahead of the command that needed it. A parametric datatype
   *  is instantiated the same way, sort by sort: `(List Int)` is a datatype
   *  named as written, with constructors `nil@Int` and `cons@Int`
   *  ([[instantiate]]). A use whose parameters the arguments do not determine
   *  must say `(as f τ)`; an assertion cannot stand for every sort.
   */
  private enum Poly:
    /** A declared function, constructor or selector: parameters, argument sorts
     *  and result, as written.
     */
    case Fun(params: List[String], args: List[SExpr], result: SExpr)

    /** A `define-fun` whose rank has parameters: its formals, result and body
     *  are read again per instance.
     */
    case Macro(params: List[String], formals: List[(String, SExpr)], result: SExpr, body: SExpr)
  private val sortParameters = scala.collection.mutable.LinkedHashSet.empty[String]
  private val declaredSorts = HashMap.empty[String, Int] // `declare-sort`, with its arity
  private val datatypeNames = scala.collection.mutable.HashSet.empty[String] // monomorphic datatypes
  private val sortDefinitions = HashMap.empty[String, (List[String], SExpr)] // define-sort
  private val polymorphic = HashMap.empty[String, Poly]
  private val templates = HashMap.empty[String, (List[String], List[SExpr])] // parametric datatypes
  private val owner = HashMap.empty[String, String] // a parametric constructor or selector to its datatype
  private val instantiated = scala.collection.mutable.HashSet.empty[String] // datatype instances, by sort text
  private val pending = scala.collection.mutable.ArrayBuffer.empty[Command] // instances' declarations
  private var sortSubst: Map[String, SExpr] = Map.empty // a template's parameters, while instantiating

  // A declaration or a definition belongs to the level it was made at and goes with the level's `pop`,
  // unless `:global-declarations` is true (issue 40): one list of undos per open level.
  private var globalDeclarations = false
  private val scopes = scala.collection.mutable.ArrayBuffer.empty[scala.collection.mutable.ArrayBuffer[() => Unit]]

  /** Records, before `map(key)` is set, how to restore it at the level's pop.
   */
  private def undoable[V](map: scala.collection.mutable.Map[String, V], key: String): Unit =
    if scopes.nonEmpty && !globalDeclarations then
      val previous = map.get(key)
      scopes.last += (() => previous.fold(map -= key)(v => map(key) = v))

  /** Records, before `key` joins `set`, its removal at the level's pop. */
  private def undoable(set: scala.collection.mutable.Set[String], key: String): Unit =
    if scopes.nonEmpty && !globalDeclarations && !set(key) then scopes.last += (() => set -= key)

  private def push(levels: Int): Unit =
    for _ <- 1 to levels do scopes += scala.collection.mutable.ArrayBuffer.empty

  private def pop(levels: Int): Unit =
    for _ <- 1 to (levels min scopes.length) do scopes.remove(scopes.length - 1).reverseIterator.foreach(_())

  // `(exit)` ends the script: what follows is not read (issue 52), as z3 and cvc5 stop there.
  private var exited = false

  def parse(input: String): Script = Script(SExprParser.parse(input).flatMap { s =>
    if exited then Nil
    else
      val commands = command(s)
      val out = pending.toList ++ commands
      pending.clear()
      wellFounded(out.collect { case Command.DeclareDatatypes(datatypes) => datatypes }.flatten)
      out
  })

  private def command(sexpr: SExpr): List[Command] = sexpr match
    case SList(SSymbol("set-logic") :: SSymbol(logic) :: Nil) => List(Command.SetLogic(logic))
    case SList(SSymbol("set-info") :: SKeyword(key) :: value :: Nil) => List(Command.SetInfo(s":$key", value.toString))
    case SList(SSymbol("declare-sort") :: SSymbol(name) :: SNumeral(arity) :: Nil) =>
      undoable(declaredSorts, name)
      declaredSorts(name) = index(arity)
      List(Command.DeclareSort(name, index(arity)))
    case SList(SSymbol("declare-sort") :: SSymbol(name) :: Nil) =>
      undoable(declaredSorts, name)
      declaredSorts(name) = 0
      List(Command.DeclareSort(name, 0))
    case SList(SSymbol("declare-sort-parameter") :: SSymbol(name) :: Nil) =>
      undoable(sortParameters, name)
      sortParameters += name
      Nil
    case SList(SSymbol("define-sort") :: SSymbol(name) :: SList(params) :: body :: Nil) =>
      undoable(sortDefinitions, name)
      sortDefinitions(name) =
        (params.map { case SSymbol(p) => p; case other => throw Smt2Error(s"bad parameter $other") }, body)
      Nil
    case SList(SSymbol("declare-fun") :: SSymbol(name) :: SList(args) :: s :: Nil) => declare(name, args, s)
    case SList(SSymbol("define-const") :: SSymbol(name) :: s :: body :: Nil) => // a `define-fun` of no parameter
      command(SList(List(SSymbol("define-fun"), SSymbol(name), SList(Nil), s, body)))
    case SList(SSymbol("declare-const") :: SSymbol(name) :: s :: Nil) => declare(name, Nil, s)
    case SList(SSymbol("declare-datatype") :: SSymbol(name) ::
          SList(SSymbol("par") :: SList(params) :: SList(constructors) :: Nil) :: Nil) =>
      template(name, params, constructors)
      Nil
    case SList(SSymbol("declare-datatype") :: SSymbol(name) :: SList(constructors) :: Nil) =>
      List(declareDatatypes(List((name, constructors))))
    case SList(SSymbol("declare-datatypes") :: SList(names) :: SList(declarations) :: Nil)
        if names.exists { case SList(_ :: SNumeral(n) :: Nil) if n == 0 => false; case _ => true } =>
      // Parametric: each declaration is `(par (params) (constructors))`, a template instantiated on use.
      // A monomorphic member is named up front: an earlier member's field may mention it.
      for case SList(SSymbol(name) :: SNumeral(n) :: Nil) <- names if n == 0 do
        undoable(datatypeNames, name)
        datatypeNames += name
      for (n, d) <- names.zip(declarations) do
        (n, d) match
          case (
                SList(SSymbol(name) :: SNumeral(_) :: Nil),
                SList(SSymbol("par") :: SList(params) :: SList(constructors) :: Nil)
              ) =>
            template(name, params, constructors)
          case (
                SList(SSymbol(name) :: SNumeral(_) :: Nil),
                SList(constructors)
              ) => // a monomorphic member of the group
            command(SList(List(SSymbol("declare-datatype"), SSymbol(name), SList(constructors)))).foreach(pending += _)
          case other => throw Smt2Error(s"bad datatype declaration $other")
      Nil
    case SList(SSymbol("declare-datatypes") :: SList(names) :: SList(declarations) :: Nil) =>
      val sorts = names.map {
        case SList(SSymbol(name) :: SNumeral(_) :: Nil) => name
        case other => throw Smt2Error(s"bad datatype declaration $other")
      }
      if sorts.length != declarations.length then
        throw Smt2Error("declare-datatypes: as many declarations as sorts expected")
      List(declareDatatypes(sorts.zip(declarations.map {
        case SList(constructors) => constructors
        case other => throw Smt2Error(s"bad constructor list $other")
      })))
    case SList(SSymbol("define-fun") :: SSymbol(name) :: SList(params) :: s :: body :: Nil)
        if sortParameters.exists(p => mentions(s, p) || params.exists(mentions(_, p))) =>
      free(name)
      val formals = params.map {
        case SList(SSymbol(p) :: ps :: Nil) => (p, ps)
        case other => throw Smt2Error(s"bad parameter $other")
      }
      val ps = sortParameters.filter(p => mentions(s, p) || formals.exists((_, fs) => mentions(fs, p))).toList
      undoable(polymorphic, name)
      polymorphic(name) = Poly.Macro(ps, formals, s, body)
      Nil
    case SList(SSymbol("define-fun") :: SSymbol(name) :: SList(params) :: s :: body :: Nil) =>
      val ps = parameters(params)
      val result = sort(s)
      check(result)
      free(name) // after the sorts, which may have instantiated a datatype whose symbol this is
      val typed = definition(ps, result, body)
      undoable(macros, name)
      macros(name) = (ps, result, typed)
      List(Command.DefineFun(name, ps, result, typed))
    case SList(SSymbol("assert") :: SList(SSymbol("!") :: body :: attributes) :: Nil)
        if attributes.sliding(2).exists { case Seq(SKeyword("named"), _) => true; case _ => false } =>
      val name = attributes.sliding(2).collectFirst { case Seq(SKeyword("named"), SSymbol(n)) => n }.get
      List(Command.AssertNamed(name, assertion(body)))
    case SList(SSymbol("assert") :: body :: Nil) => List(Command.Assert(assertion(body)))
    case SList(SSymbol("check-sat") :: Nil) => List(Command.CheckSat)
    case SList(SSymbol("check-sat-using") :: _) => List(Command.CheckSat) // z3's, with a tactic: ignored
    case SList(SSymbol("check-sat-assuming") :: SList(assumptions) :: Nil) =>
      List(Command.CheckSatAssuming(assumptions.map(assertion)))
    case SList(SSymbol("check-sat") :: assumptions) => // z3's shorthand
      List(Command.CheckSatAssuming(assumptions.map(assertion)))
    case SList(SSymbol("reset-assertions") :: Nil) => List(Command.ResetAssertions)
    case SList(SSymbol("reset") :: Nil) =>
      functions.clear()
      macros.clear()
      constructors.clear()
      declaredSorts.clear()
      datatypeNames.clear()
      sortParameters.clear()
      sortDefinitions.clear()
      polymorphic.clear()
      templates.clear()
      owner.clear()
      instantiated.clear()
      instanceSymbols.clear()
      datatypeOf.clear()
      scopes.clear()
      globalDeclarations = false
      List(Command.Reset)
    case SList(SSymbol("get-unsat-core") :: Nil) => List(Command.GetUnsatCore)
    case SList(SSymbol("get-assertions") :: Nil) => List(Command.GetAssertions)
    case SList(SSymbol(name @ ("block-model" | "block-model-values" | "get-unsat-assumptions")) :: _) =>
      throw Smt2Error(s"$name is not supported")
    case SList(SSymbol("push") :: SNumeral(n) :: Nil) =>
      push(index(n))
      List(Command.Push(index(n)))
    case SList(SSymbol("push") :: Nil) =>
      push(1)
      List(Command.Push(1))
    case SList(SSymbol("pop") :: SNumeral(n) :: Nil) =>
      pop(index(n))
      List(Command.Pop(index(n)))
    case SList(SSymbol("pop") :: Nil) =>
      pop(1)
      List(Command.Pop(1))
    case SList(SSymbol("get-model") :: Nil) => List(Command.GetModel)
    case SList(SSymbol("get-value") :: SList(items) :: Nil) =>
      // An item outside the fragment (another theory's term) leaves the whole command unanswered, as before.
      try
        List(Command.GetValue(items.map(s =>
          s.toString ->
            (s match
              case SSymbol(name) if functions.get(name).flatMap(_.arrow).exists(_._1.nonEmpty) =>
                Term.Const(name) // a function symbol: its graph in the model, answered as a lambda (issue 50)
              case _ =>
                if sortOf(s, Map.empty) == Sort.Bool then assertion(s)
                else
                  val t = term(s, Map.empty)
                  sortCheck.term(t, Map.empty)
                  t)
        )))
      catch case _: Smt2Error => List(Command.Other(sexpr))
    case SList(SSymbol("set-option") :: SKeyword(key) :: value :: Nil) =>
      if key == "global-declarations" then globalDeclarations = value.toString == "true"
      List(Command.SetOption(s":$key", value.toString))
    case SList(SSymbol("get-info") :: SKeyword(key) :: Nil) => List(Command.GetInfo(s":$key"))
    case SList(SSymbol("exit") :: Nil) =>
      exited = true
      List(Command.Exit)
    case SList(SSymbol(_) :: _) => List(Command.Other(sexpr))
    case other => throw Smt2Error(s"not a command: $other")

  /** A closed formula, its sorts checked. */
  private def assertion(sexpr: SExpr): Formula =
    val f = formula(sexpr, Map.empty)
    sortCheck.formula(f, Map.empty)
    f

  /** A macro's body, its sorts checked against its parameters and result. */
  private def definition(params: List[(String, Sort)], result: Sort, body: SExpr): Term | Formula =
    val env = params.toMap
    if result == Sort.Bool then
      val f = formula(body, env)
      sortCheck.formula(f, env)
      f
    else
      val t = term(body, env)
      sortCheck.expect(sortCheck.term(t, env), result, "the body of a definition")
      t

  /** Declares `name`, with its sort as written; a rank with sort parameters
   *  declares nothing yet (see [[Poly]]).
   */
  /** Refuses a script's declaration of a symbol an instantiated datatype owns.
   */
  private def free(name: String): Unit =
    if Parser.reserved(name) then throw Smt2Error(s"$name: a reserved word; pick another name")
    if instanceSymbols(name) then throw Smt2Error(s"$name: the symbol of an instance; pick another name")

  private def declare(name: String, args: List[SExpr], s: SExpr): List[Command] =
    free(name)
    val params = sortParameters.filter(p => (s :: args).exists(mentions(_, p))).toList
    if params.nonEmpty then
      undoable(polymorphic, name)
      polymorphic(name) = Poly.Fun(params, args, s)
      Nil
    else
      val (argSorts, result) = (args.map(sort), sort(s))
      (result :: argSorts).foreach(check)
      free(name) // again: the sorts just read may have instantiated a datatype whose symbol this is
      undoable(functions, name)
      functions(name) = Sort.fun(argSorts, result)
      List(Command.DeclareFun(name, argSorts, result))

  /** Whether the symbol `p` occurs in a sort as written. A sort holds numerals
   *  as well as symbols — `(_ BitVec 8)` — and a numeral is no symbol.
   */
  private def mentions(s: SExpr, p: String): Boolean = s match
    case SSymbol(name) => name == p
    case SList(items) => items.exists(mentions(_, p))
    case _ => false

  private def substitute(s: SExpr, subst: Map[String, SExpr]): SExpr = s match
    case SSymbol(name) => subst.getOrElse(name, s)
    case SList(items) => SList(items.map(substitute(_, subst)))
    case _ => s

  /** Binds the parameters of `pattern` so that it reads as `actual` (a
   *  monomorphic sort), on top of `subst`; `None` when the two disagree.
   */
  private def unify(
      pattern: SExpr,
      actual: SExpr,
      params: Set[String],
      subst: Map[String, SExpr]
  ): Option[Map[String, SExpr]] =
    (pattern, actual) match
      case (SSymbol(p), _) if params(p) =>
        subst.get(p) match
          case Some(bound) => if bound == actual then Some(subst) else None
          case None => Some(subst + (p -> actual))
      case (SSymbol(a), SSymbol(b)) => if a == b then Some(subst) else None
      case (SList(ps), SList(as)) if ps.length == as.length =>
        ps.zip(as).foldLeft(Option(subst)) { case (acc, (p, a)) => acc.flatMap(unify(p, a, params, _)) }
      case _ => None

  private def sexprOf(s: Sort): SExpr = SExprParser.parse(s.text).head

  /** The name of a monomorphic symbol: `name` itself, or the instance of a
   *  polymorphic one at the arguments' sorts (and the sort `expected` of the
   *  result, from `(as name τ)`), declared here if new.
   */
  private def instance(name: String, argSorts: List[Sort], expected: Option[Sort]): String =
    polymorphic.get(name) match
      case None =>
        val declared = functions.get(name).map(s => s.arrow.fold(s)(_._2)).orElse(macros.get(name).map(_._2))
        for e <- expected; s <- declared if s != e do throw Smt2Error(s"(as $name ${e.text}): its sort is ${s.text}")
        name
      case Some(poly) =>
        val (params, args, result) = poly match
          case Poly.Fun(ps, as, r) => (ps, as, r)
          case Poly.Macro(ps, formals, r, _) => (ps, formals.map(_._2), r)
        if args.length != argSorts.length then throw Smt2Error(s"$name expects ${args.length} arguments")
        val pairs = args.zip(argSorts.map(sexprOf)) ++ expected.map(e => (result, sexprOf(e))).toList
        val subst = pairs.foldLeft(Option(Map.empty[String, SExpr])) { case (acc, (p, a)) =>
          acc.flatMap(unify(p, a, params.toSet, _))
        }.getOrElse(throw Smt2Error(
          s"$name is not applicable to ${argSorts.mkString(" ")}${expected.map(" as " + _).getOrElse("")}"
        ))
        val actual = params.map(p =>
          subst.getOrElse(
            p,
            throw Smt2Error(s"$name: the sort parameter $p is not determined here, write (as $name τ)")
          )
        )
        val actualSorts = actual.map(sort)
        val instanceName = mangle(name, actualSorts)
        owner.get(name) match
          case Some(datatype) =>
            instantiate(datatype, actualSorts) // declares the instance's constructors and selectors
          case None =>
            // The instance's name lives in the script's namespace, like a datatype instance's symbols
            // (issue 21): a script symbol of that name is refused, in either order (issue 43).
            if (functions.contains(instanceName) || macros.contains(instanceName)) && !instanceSymbols(instanceName)
            then throw Smt2Error(s"$instanceName: the script's symbol clashes with the instance of $name")
            if !instanceSymbols(instanceName) then
              undoable(instanceSymbols, instanceName)
              instanceSymbols += instanceName
              val saved = sortSubst
              sortSubst = params.zip(actual).toMap
              try
                poly match
                  case Poly.Fun(_, as, r) =>
                    val (argSorts, resultSort) = (as.map(sort), sort(r))
                    (resultSort :: argSorts).foreach(check)
                    undoable(functions, instanceName)
                    functions(instanceName) = Sort.fun(argSorts, resultSort)
                    pending += Command.DeclareFun(instanceName, argSorts, resultSort)
                  case Poly.Macro(_, formals, r, body) =>
                    val ps = formals.map((n, s) => n -> sort(s))
                    val resultSort = sort(r)
                    (resultSort :: ps.map(_._2)).foreach(check)
                    val typed = definition(ps, resultSort, body)
                    undoable(macros, instanceName)
                    macros(instanceName) = (ps, resultSort, typed)
                    pending += Command.DefineFun(instanceName, ps, resultSort, typed)
              finally sortSubst = saved
        instanceName

  /** The name of the instance of `name` at the sorts `args`: `name@τ1@…`. */
  private def mangle(name: String, args: List[Sort]): String = s"$name@${args.map(_.text).mkString("@")}"

  /** The instance of a parametric datatype at the sorts `args`, declared with
   *  its constructors and selectors on first use: the sort `(name args)`, the
   *  symbols `c@args`.
   */
  private def instantiate(name: String, args: List[Sort]): Sort =
    val (params, decls) = templates(name)
    if args.length != params.length then throw Smt2Error(s"$name takes ${params.length} sort arguments")
    val text = s"($name ${args.map(_.text).mkString(" ")})"
    if !instantiated(text) then
      undoable(instantiated, text)
      instantiated += text
      val saved = sortSubst
      sortSubst = params.zip(args.map(sexprOf)).toMap
      try
        val datatype = Datatype(
          text,
          decls.map {
            case SList(SSymbol(constructor) :: selectors) =>
              Constructor(
                mangle(constructor, args),
                selectors.map {
                  case SList(SSymbol(selector) :: s :: Nil) => (mangle(selector, args), sort(s))
                  case other => throw Smt2Error(s"bad selector $other")
                }
              )
            case other => throw Smt2Error(s"bad constructor $other")
          }
        )
        // The instance's symbols, `c@Int`, live in the script's namespace: a script symbol of that
        // name is refused, in either order (issue 21).
        val symbols = datatype.constructors.flatMap(c => c.name :: c.tester :: c.selectors.map(_._1))
        for symbol <- symbols if functions.contains(symbol) && !instanceSymbols(symbol) do
          throw Smt2Error(s"$symbol: the script's symbol clashes with the instance $text of $name")
        for symbol <- symbols do undoable(instanceSymbols, symbol)
        instanceSymbols ++= symbols
        register(datatype)
        fields(datatype)
        pending += Command.DeclareDatatypes(List(datatype))
      finally sortSubst = saved
    Sort.Named(text)

  /** Declares datatypes: their constructors, selectors and testers become
   *  function symbols (a constructor `C` of datatype `D` with selectors
   *  `(s_i S_i)` is `C : S_1 ... S_n -> D`, `s_i : D -> S_i` and the tester
   *  `(_ is C)` : `D -> Bool`).
   */
  private def declareDatatypes(declarations: List[(String, List[SExpr])]): Command =
    for (name, constructors) <- declarations do distinct(name, constructors)
    for (name, _) <- declarations do // named first: the fields read below may mention them, and instantiate
      undoable(datatypeNames, name)
      datatypeNames += name
    val datatypes = declarations.map { (name, constructors) =>
      Datatype(
        name,
        constructors.map {
          case SList(SSymbol(constructor) :: selectors) =>
            Constructor(
              constructor,
              selectors.map {
                case SList(SSymbol(selector) :: s :: Nil) => (selector, sort(s))
                case other => throw Smt2Error(s"bad selector $other")
              }
            )
          case other => throw Smt2Error(s"bad constructor $other")
        }
      )
    }
    datatypes.foreach(register)
    datatypes.foreach(fields)
    Command.DeclareDatatypes(datatypes)

  /** Refuses a datatype that declares a constructor or a selector twice, as z3
   *  and cvc5 do (issue 146): the second declaration would replace the first, a
   *  selector `f` of two constructors being one function symbol here.
   */
  private def distinct(datatype: String, constructors: List[SExpr]): Unit =
    val names = constructors.collect { case SList(SSymbol(constructor) :: _) => constructor }
    val selectors = constructors.collect { case SList(_ :: fields) => fields }.flatten
      .collect { case SList(SSymbol(selector) :: _) => selector }
    for name <- names.diff(names.distinct).headOption do
      throw Smt2Error(s"$name: a constructor declared twice in the datatype $datatype")
    for name <- selectors.diff(selectors.distinct).headOption do
      throw Smt2Error(s"$name: a selector declared twice in the datatype $datatype")

  /** Refuses datatypes that are not well-founded, as SMT-LIB asks and as z3 and
   *  cvc5 do (issue 147): a datatype has values only if one of its constructors
   *  takes fields that all have some. `datatypes` are the ones a command
   *  declared, with the instances of parametric datatypes it made — a
   *  parametric datatype is judged there, instance by instance. The sorts
   *  declared before have values, and so the least fixpoint is over these: the
   *  datatypes left once no other can be given a value have none. An array has
   *  values when its indices and its elements do, which is the rule of the two.
   */
  private def wellFounded(datatypes: List[Datatype]): Unit =
    def without(open: List[Datatype]): List[Datatype] =
      val names = open.map(_.name).toSet
      def inhabited(s: Sort): Boolean = s match
        case Sort.Named(name) => !names(name)
        case Sort.Array(index, element) => inhabited(index) && inhabited(element)
        case _ => true
      val rest = open.filterNot(_.constructors.exists(_.selectors.forall((_, s) => inhabited(s))))
      if rest.length == open.length then open else without(rest)
    for datatype <- without(datatypes).headOption do
      throw Smt2Error(s"the datatype ${datatype.name} is not well-founded: none of its constructors has a value")

  /** Makes a datatype's constructors, selectors and testers known. */
  private def register(datatype: Datatype): Unit =
    val d = Sort.Named(datatype.name)
    for constructor <- datatype.constructors do
      undoable(constructors, constructor.name)
      constructors(constructor.name) = constructor
      undoable(datatypeOf, constructor.name)
      datatypeOf(constructor.name) = datatype.name
      undoable(functions, constructor.name)
      functions(constructor.name) = Sort.fun(constructor.selectors.map(_._2), d)
      undoable(functions, constructor.tester)
      functions(constructor.tester) = Sort.fun(List(d), Sort.Bool)
      for (selector, s) <- constructor.selectors do
        undoable(functions, selector)
        functions(selector) = Sort.fun(List(d), s)

  /** Keeps a parametric datatype's declaration for its instances, and makes its
   *  constructors and selectors polymorphic symbols of the datatype.
   */
  private def template(name: String, params: List[SExpr], constructors: List[SExpr]): Unit =
    val ps = params.map { case SSymbol(p) => p; case other => throw Smt2Error(s"bad sort parameter $other") }
    distinct(name, constructors)
    undoable(templates, name)
    templates(name) = (ps, constructors)
    val self = SList(SSymbol(name) :: ps.map(SSymbol(_)))
    for c <- constructors do
      c match
        case SList(SSymbol(constructor) :: selectors) =>
          val fields = selectors.map {
            case SList(SSymbol(selector) :: s :: Nil) =>
              undoable(polymorphic, selector)
              polymorphic(selector) = Poly.Fun(ps, List(self), s)
              undoable(owner, selector)
              owner(selector) = name
              s
            case other => throw Smt2Error(s"bad selector $other")
          }
          undoable(polymorphic, constructor)
          polymorphic(constructor) = Poly.Fun(ps, fields, self)
          undoable(owner, constructor)
          owner(constructor) = name
        case other => throw Smt2Error(s"bad constructor $other")

  private def sort(s: SExpr): Sort = s match
    case SSymbol(name) if sortSubst.contains(name) => sort(sortSubst(name))
    case SSymbol(name) if sortDefinitions.get(name).exists(_._1.isEmpty) => sort(sortDefinitions(name)._2)
    case SList(SSymbol(name) :: args) if sortDefinitions.contains(name) =>
      val (params, body) = sortDefinitions(name)
      if args.length != params.length then throw Smt2Error(s"$name takes ${params.length} sort arguments")
      sort(substitute(body, params.zip(args).toMap))
    case SList(SSymbol(name) :: args) if templates.contains(name) => instantiate(name, args.map(sort))
    case SSymbol("Bool") => Sort.Bool
    case SSymbol("Int") => Sort.Int
    case SSymbol("Real") => Sort.Real
    case SSymbol(name) if declaredSorts.get(name).exists(_ > 0) =>
      throw Smt2Error(s"the sort $name takes ${declaredSorts(name)} sort arguments")
    case SSymbol(name) => Sort.Named(name)
    case SList(SSymbol("_") :: SSymbol("BitVec") :: SNumeral(width) :: Nil) => Sort.BitVec(index(width))
    case SList(SSymbol("Array") :: args) if args.length >= 2 =>
      val sorts = args.map(sort)
      sorts.init.foldRight(sorts.last)(Sort.Array(_, _))
    // An instance of a declared sort constructor, named by its arguments' own sorts: `(Box X)` under a
    // sort parameter and `(Box IntBox)` under `define-sort` are the same sort as `(Box Int)`.
    case SList(SSymbol(name) :: args) if declaredSorts.contains(name) && args.nonEmpty =>
      if args.length != declaredSorts(name) then
        throw Smt2Error(s"the sort $name takes ${declaredSorts(name)} sort arguments")
      Sort.Named(s"($name ${args.map(sort(_).text).mkString(" ")})")
    case other => Sort.Named(other.toString) // rejected by `check` where a symbol is declared

  /** Whether the script declared the sort `name`: a sort, a datatype, or an
   *  instance of a sort constructor or of a parametric datatype.
   */
  private def known(name: String): Boolean =
    declaredSorts.contains(name) || datatypeNames(name) || instantiated(name)
      || (name.startsWith("(") && declaredSorts.contains(name.drop(1).takeWhile(_ != ' ')))

  /** A sort of a theory that is not spoken here: strings, floats, sets, ... */
  private def unsupported(name: String): Boolean =
    List(
      "String",
      "RegLan",
      "RoundingMode",
      "(RoundingMode)",
      "UnitTuple",
      "(Set ",
      "(Bag ",
      "(Seq ",
      "(Tuple ",
      "(_ FloatingPoint"
    )
      .exists(u => name == u || name.startsWith(u)) || name.startsWith("Float")

  /** Rejects, at a declaration or a binder, a sort the script did not declare,
   *  which would otherwise pass for an uninterpreted sort, and the unsupported
   *  ones.
   */
  private def check(s: Sort): Unit = s match
    case Sort.Named(name) if known(name) => ()
    case Sort.Named(name) =>
      if unsupported(name) then throw Smt2Error(s"the sort $name is not supported")
      throw Smt2Error(s"unknown sort $name")
    case Sort.Array(index, element) =>
      check(index)
      check(element)
    case _ => ()

  /** Rejects a datatype's field of an undeclared sort. An unsupported one
   *  stays, as before: an unused field costs nothing.
   */
  private def fields(datatype: Datatype): Unit =
    def field(s: Sort): Unit = s match
      case Sort.Named(name) if !known(name) && !unsupported(name) => throw Smt2Error(s"unknown sort $name")
      case Sort.Array(index, element) =>
        field(index)
        field(element)
      case _ => ()
    for constructor <- datatype.constructors; (_, s) <- constructor.selectors do field(s)

  /** The parameters of a macro, `((x S) ...)`, with their sorts.
   */
  private def parameters(params: List[SExpr]): List[(String, Sort)] = params.map {
    case SList(SSymbol(p) :: s :: Nil) =>
      val parsed = sort(s)
      check(parsed)
      (p, parsed)
    case other => throw Smt2Error(s"bad parameter $other")
  }

  private def isNumeral(name: String): Boolean = name.nonEmpty && name.forall(_.isDigit)

  private def isDecimal(name: String): Boolean =
    val i = name.indexOf('.')
    i > 0 && i < name.length - 1 && name.take(i).forall(_.isDigit) && name.drop(i + 1).forall(_.isDigit)

  /** The sort of an expression: what decides between the two trees. `env` binds
   *  the `let`-bound names in scope.
   */
  /** Whether `name` at the head of a list is the script's own function or
   *  macro: a script may declare `+` or `to_real` in a logic without the theory
   *  (issue 41), and its symbol is then not the operator.
   */
  private def scripted(name: String, env: Map[String, Sort]): Boolean =
    !env.contains(name) && (functions.contains(name) || macros.contains(name))

  private def sortOf(sexpr: SExpr, env: Map[String, Sort]): Sort = sexpr match
    case SSymbol("true" | "false") => Sort.Bool
    case SList(SSymbol(name) :: args) if scripted(name, env) =>
      macros.get(name).map(_._2).getOrElse(applied(functions(name), args.length))
    case SNumeral(_) => Sort.Int
    case SDecimal(_, _) => Sort.Real
    case SBits(_, width, _) => Sort.BitVec(width)
    case SList(SSymbol("_") :: SSymbol(literal) :: SNumeral(width) :: Nil)
        if literal.startsWith("bv") && isNumeral(literal.drop(2)) =>
      Sort.BitVec(index(width))
    case SSymbol(name) =>
      env.get(name).orElse(functions.get(name)).orElse(macros.get(name).map(_._2)).getOrElse(
        if polymorphic.contains(name) then symbolSort(instance(name, Nil, None))
        else throw Smt2Error(s"unknown symbol $name")
      )
    case SList(SList(SSymbol("as") :: SSymbol("const") :: s :: Nil) :: _ :: Nil) if constantArray(s, env) => sort(s)
    case SList(SSymbol("as") :: SSymbol(name) :: s :: Nil) => symbolSort(instance(name, Nil, Some(sort(s))))
    case SList(SList(SSymbol("as") :: SSymbol(name) :: s :: Nil) :: args) =>
      resultSort(instance(name, args.map(sortOf(_, env)), Some(sort(s))), args.length)
    case SList(SSymbol("bvcomp") :: _) => Sort.BitVec(1)
    case SList(SSymbol("ubv_to_int" | "sbv_to_int" | "bv2nat" | "bv2int") :: _) => Sort.Int
    case SList(SList(SSymbol("_") :: SSymbol("int_to_bv" | "int2bv") :: SNumeral(n) :: Nil) :: _) =>
      Sort.BitVec(index(n))
    case SList(SSymbol(op) :: a :: _) if BvOp.named.contains(op) && op != "concat" => sortOf(a, env)
    case SList(SSymbol("concat") :: args) =>
      Sort.BitVec(args.map(a => width(sortOf(a, env))).sum)
    case SList(SSymbol(op) :: _) if BvCmpOp.named.contains(op) => Sort.Bool
    case SList(SList(SSymbol("_") :: SSymbol("extract") :: SNumeral(i) :: SNumeral(j) :: Nil) :: _ :: Nil) =>
      Sort.BitVec(index(i) - index(j) + 1)
    case SList(SList(SSymbol("_") :: SSymbol("zero_extend" | "sign_extend") :: SNumeral(k) :: Nil) :: a :: Nil) =>
      Sort.BitVec(width(sortOf(a, env)) + index(k))
    case SList(SList(SSymbol("_") :: SSymbol("repeat") :: SNumeral(k) :: Nil) :: a :: Nil) =>
      Sort.BitVec(width(sortOf(a, env)) * index(k))
    case SList(SList(SSymbol("_") :: SSymbol("rotate_left" | "rotate_right") :: SNumeral(_) :: Nil) :: a :: Nil) =>
      sortOf(a, env)
    case SList(SSymbol("not" | "and" | "or" | "=>" | "xor" | "=" | "distinct" | "<=" | "<" | ">=" | ">") :: _) =>
      Sort.Bool
    case SList(SSymbol("/") :: _) => Sort.Real
    case SList(SSymbol("div" | "mod" | "abs" | "to_int") :: _) => Sort.Int
    case SList(SSymbol("to_real") :: _) => Sort.Real
    case SList(SSymbol("is_int") :: _) => Sort.Bool
    case SList(SSymbol("select") :: a :: _ :: Nil) =>
      sortOf(a, env) match
        case Sort.Array(_, element) => element
        case s => throw Smt2Error(s"select on $s")
    case SList(SSymbol("store") :: a :: _ :: _ :: Nil) => sortOf(a, env)
    case SList(SSymbol("+" | "-" | "*") :: args) =>
      if args.exists(a => sortOf(a, env) == Sort.Real) then Sort.Real else Sort.Int
    case SList(SList(SSymbol("_") :: SSymbol("is") :: SSymbol(_) :: Nil) :: _ :: Nil) => Sort.Bool
    case SList(SSymbol("ite") :: _ :: thn :: _ :: Nil) => sortOf(thn, env)
    case SList(SSymbol("let") :: SList(bindings) :: body :: Nil) =>
      sortOf(
        body,
        env ++ bindings.map {
          case SList(SSymbol(name) :: value :: Nil) => name -> sortOf(value, env)
          case other => throw Smt2Error(s"bad binding $other")
        }
      )
    case SList(SSymbol("match") :: _) => sortOf(matchToIte(sexpr, env), env)
    case SList(SSymbol(name) :: args) if macros.contains(name) => macros(name)._2
    case SList(SSymbol(name) :: args) if polymorphic.contains(name) && !env.contains(name) =>
      resultSort(instance(name, args.map(sortOf(_, env)), None), args.length)
    case SList(SSymbol(name) :: args) => applied(sortOf(SSymbol(name), env), args.length)
    case other => throw Smt2Error(s"cannot type $other")

  /** The sort of a monomorphic symbol: a declared function's whole function
   *  sort, or a macro's result.
   */
  private def symbolSort(name: String): Sort =
    functions.get(name).orElse(macros.get(name).map(_._2)).getOrElse(throw Smt2Error(s"unknown symbol $name"))

  /** The sort of a monomorphic symbol applied to `n` arguments: a macro's is
   *  its result.
   */
  private def resultSort(name: String, n: Int): Sort =
    macros.get(name).map(_._2).getOrElse(applied(symbolSort(name), n))

  /** A numeral that must fit an `Int`: an index, a width, a count. Read
   *  truncated, `(_ rotate_left 4294967296)` was a rotation by nothing (issue
   *  44).
   */
  private def index(n: BigInt): Int =
    if n.isValidInt then n.toInt else throw Smt2Error(s"$n: too large for an index")

  private def width(s: Sort): Int = s match
    case Sort.BitVec(w) => w
    case _ => throw Smt2Error(s"a bit-vector was expected, not $s")

  private def applied(s: Sort, n: Int): Sort =
    s.applied(n).getOrElse(throw Smt2Error(s"$s applied to $n arguments"))

  private def formula(sexpr: SExpr, env: Map[String, Sort]): Formula = sexpr match
    case SSymbol("true") => True
    case SSymbol("false") => False
    case SList(SSymbol(name) :: _) if scripted(name, env) => predicate(sexpr, env)
    case SList(SSymbol(q @ ("forall" | "exists")) :: _) => throw Smt2Error(s"$q: quantifiers are not supported")
    case SList(SSymbol("not") :: arg :: Nil) => Not(formula(arg, env))
    case SList(SSymbol("and") :: args) => And(args.map(formula(_, env)))
    case SList(SSymbol("or") :: args) => Or(args.map(formula(_, env)))
    case SList(SSymbol("=>") :: args) if args.length >= 2 => Implies(args.map(formula(_, env)))
    case SList(SSymbol("xor") :: args) if args.length >= 2 => Xor(args.map(formula(_, env)))
    case SList(SSymbol("=") :: args) if args.length >= 2 =>
      if sortOf(args.head, env) == Sort.Bool then Iff(args.map(formula(_, env)))
      else Eq(args.map(term(_, env)))
    case SList(SSymbol("distinct") :: args) => Distinct(args.map(term(_, env)))
    case SList(SSymbol(op) :: a :: b :: Nil) if BvCmpOp.named.contains(op) =>
      BvCmp(BvCmpOp.named(op), term(a, env), term(b, env))
    case SList(SList(SSymbol("_") :: SSymbol("is") :: SSymbol(constructor) :: Nil) :: arg :: Nil) =>
      // A parametric constructor's tester is the instance's, found by the argument's sort: the
      // constructor itself is not applied here, so its arity is not the question (issue 31).
      val c =
        if owner.contains(constructor) then
          val text = sortOf(arg, env).text
          constructors.keys.find(m => datatypeOf.get(m).contains(text) && m.startsWith(s"$constructor@"))
            .getOrElse(throw Smt2Error(s"$constructor is not a constructor of $text"))
        else constructor
      declared(s"(_ is $c)", env)
      IsConstructor(c, term(arg, env))
    case SList(SSymbol("is_int") :: arg :: Nil) => IsInt(term(arg, env))
    case SList(SSymbol(op @ ("<=" | "<" | ">=" | ">")) :: args) if args.length >= 2 =>
      Cmp(CmpOp.values.find(_.name == op).get, args.map(term(_, env)))
    case SList(SSymbol("ite") :: cond :: thn :: els :: Nil) =>
      Ite(formula(cond, env), formula(thn, env), formula(els, env))
    case SList(SSymbol("let") :: SList(bs) :: body :: Nil) =>
      val (bound, inner) = bindings(bs, env)
      Let(bound, formula(body, inner))
    case SList(SSymbol("match") :: _) => formula(matchToIte(sexpr, env), env)
    case SList(SSymbol("!") :: body :: _) => formula(body, env) // an annotated term
    case _ => predicate(sexpr, env)
  end formula

  /** A Boolean constant or application as a formula. */
  private def predicate(sexpr: SExpr, env: Map[String, Sort]): Formula =
    if sortOf(sexpr, env) != Sort.Bool then throw Smt2Error(s"not a formula: $sexpr")
    Formula.Pred(term(sexpr, env))

  /** `(match t ((p1 b1) ... (pn bn)))` as the tree the rest of the parser
   *  reads: the scrutinee bound once by a `let` — so it is shared, as `let`
   *  bindings are — then an `ite` per case on the constructor's tester, its
   *  body under a `let` binding the pattern's variables to the selectors; the
   *  last case is the default (the cases are exhaustive), and a variable
   *  pattern binds the scrutinee itself and ends the cases. A pattern symbol
   *  that names a constructor is that constructor; any other is a variable.
   */
  private def matchToIte(sexpr: SExpr, env: Map[String, Sort]): SExpr = sexpr match
    case SList(SSymbol("match") :: scrutinee :: SList(cases) :: Nil) if cases.nonEmpty =>
      matches += 1
      // Past the script's own symbols (issue 21), and the names bound around the match — a `let`'s, a
      // macro's parameters — which a case body may read (issue 42).
      while functions.contains(s"match!$matches") || macros.contains(s"match!$matches") ||
        env.contains(s"match!$matches")
      do matches += 1
      val name = s"match!$matches"
      val m = SSymbol(name)
      // A symbol pattern is a constructor pattern only for a constructor of the scrutinee's datatype;
      // any other symbol is a variable that binds the whole scrutinee (issue 23). The scrutinee's sort
      // is asked for when it can be told here, before the `let`s around it are read.
      val scrutineeSort = scala.util.Try(sortOf(scrutinee, env).text).toOption // a macro's parameter too
      def binding(name: String, value: SExpr): SExpr = SList(List(SSymbol(name), value))
      def let(bindings: List[SExpr], body: SExpr): SExpr =
        if bindings.isEmpty then body else SList(List(SSymbol("let"), SList(bindings), body))
      def isConstructor(name: String): Boolean = scrutineeSort match
        case Some(d) =>
          datatypeOf.get(name).contains(d) ||
          owner.get(name).exists(o => d.startsWith(s"($o ") && polymorphic.contains(name))
        case None => constructors.contains(name) || owner.contains(name) && polymorphic.contains(name)
      def selectorsOf(name: String): List[String] = constructors.get(name) match
        case Some(c) => c.selectors.map(_._1)
        case None => // a parametric constructor: its declaration in the template
          templates(owner(name))._2.collectFirst {
            case SList(SSymbol(`name`) :: selectors) =>
              selectors.map { case SList(SSymbol(s) :: _) => s; case _ => "?" }
          }.getOrElse(Nil)
      def branch(c: SExpr): (Option[SExpr], SExpr) = c match // the tester, or none for a variable, and the body
        case SList(SSymbol(name) :: body :: Nil) if isConstructor(name) =>
          (Some(SList(List(SList(List(SSymbol("_"), SSymbol("is"), SSymbol(name))), m))), body)
        case SList(SSymbol(name) :: body :: Nil) => (None, let(List(binding(name, m)), body))
        case SList(SList(SSymbol(name) :: vars) :: body :: Nil) if isConstructor(name) =>
          val selectors = selectorsOf(name)
          if vars.length != selectors.length then throw Smt2Error(s"$name takes ${selectors.length} arguments: $c")
          val bound = vars.zip(selectors).flatMap {
            case (SSymbol("_"), _) => None // a wildcard binds nothing
            case (SSymbol(v), selector) => Some(binding(v, SList(List(SSymbol(selector), m))))
            case (other, _) => throw Smt2Error(s"bad pattern variable $other")
          }
          (Some(SList(List(SList(List(SSymbol("_"), SSymbol("is"), SSymbol(name))), m))), let(bound, body))
        case other => throw Smt2Error(s"bad match case $other")
      val branches = cases.map(branch)
      // Up to the first variable pattern, which catches everything after it.
      val reached = branches.indexWhere(_._1.isEmpty) match
        case -1 => branches
        case i => branches.take(i + 1)
      val body = reached.init.foldRight(reached.last._2) { case ((tester, body), rest) =>
        SList(List(SSymbol("ite"), tester.get, body, rest))
      }
      let(List(binding(name, scrutinee)), body)
    case other => throw Smt2Error(s"bad match $other")

  /** The bindings of a `let`, each typed by its own sort, and the environment
   *  for the body.
   */
  private def bindings(bs: List[SExpr], env: Map[String, Sort]): (List[(String, Term | Formula)], Map[String, Sort]) =
    val bound = bs.map {
      case SList(SSymbol(name) :: value :: Nil) =>
        val s = sortOf(value, env)
        val v: Term | Formula = if s == Sort.Bool then formula(value, env) else term(value, env)
        (name, s, v)
      case other => throw Smt2Error(s"bad binding $other")
    }
    (bound.map((name, _, v) => (name, v)), env ++ bound.map((name, s, _) => name -> s))

  private def term(sexpr: SExpr, env: Map[String, Sort]): Term = sexpr match
    case SSymbol("true") => Term.Bool(True)
    case SSymbol("false") => Term.Bool(False)
    case SList(SSymbol(name) :: args) if scripted(name, env) => application(name, args, env)
    case SList(SSymbol(q @ ("forall" | "exists")) :: _) => throw Smt2Error(s"$q: quantifiers are not supported")
    // A formula-shaped tree where a term is expected (an argument, a field).
    case SList(SSymbol("not" | "and" | "or" | "=>" | "xor" | "distinct" | "<=" | "<" | ">=" | ">" | "is_int") :: _) =>
      Term.Bool(formula(sexpr, env))
    case SList(SSymbol("=") :: _ :: _ :: _) => Term.Bool(formula(sexpr, env))
    case SList(SSymbol(op) :: _ :: _ :: Nil) if BvCmpOp.named.contains(op) => Term.Bool(formula(sexpr, env))
    case SList(SList(SSymbol("_") :: SSymbol("is") :: SSymbol(_) :: Nil) :: _ :: Nil) => Term.Bool(formula(sexpr, env))
    case SNumeral(value) => Term.Numeral(value)
    case SDecimal(unscaled, scale) => Term.Decimal(unscaled, scale)
    case SBits(value, width, _) => Term.Bits(value, width)
    case SList(SSymbol("_") :: SSymbol(literal) :: SNumeral(width) :: Nil)
        if literal.startsWith("bv") && isNumeral(literal.drop(2)) =>
      Term.Bits(BigInt(literal.drop(2)).mod(BigInt(2).pow(index(width))), index(width))
    case SSymbol(name) =>
      declared(name, env)
      val concrete = if !env.contains(name) then instance(name, Nil, None) else name
      if !env.contains(name) then // a function symbol is applied, never a value
        val params =
          macros.get(concrete).map(_._1.length).orElse(functions.get(concrete).flatMap(_.arrow).map(_._1.length))
        params.filter(_ > 0).foreach(n => throw Smt2Error(s"$name expects $n arguments"))
      Term.Const(concrete)
    case SList(SList(SSymbol("as") :: SSymbol("const") :: s :: Nil) :: v :: Nil) if constantArray(s, env) =>
      Term.ConstArray(sort(s), term(v, env))
    case SList(SSymbol("as") :: SSymbol(name) :: s :: Nil) => Term.Const(instance(name, Nil, Some(sort(s))))
    case SList(SList(SSymbol("as") :: SSymbol(name) :: s :: Nil) :: args) =>
      Term.App(Term.Const(instance(name, args.map(sortOf(_, env)), Some(sort(s)))), args.map(term(_, env)))
    case SList(SSymbol(op) :: args) if BvOp.named.contains(op) => Term.BvApp(BvOp.named(op), args.map(term(_, env)))
    case SList(SList(SSymbol("_") :: SSymbol(op) :: indices) :: args)
        if BvOp.indexed(op, indices.collect { case SNumeral(i) => index(i) }).isDefined =>
      val parsed = BvOp.indexed(op, indices.collect { case SNumeral(i) => index(i) }).get
      Term.BvApp(parsed, args.map(term(_, env)))
    case SList(SSymbol("select") :: a :: i :: Nil) if selectable(a, env) =>
      Term.Select(term(a, env), term(i, env))
    case SList(SSymbol("store") :: a :: i :: v :: Nil) if selectable(a, env) =>
      Term.Store(term(a, env), term(i, env), term(v, env))
    case SList(SSymbol("-") :: arg :: Nil) => Term.ArithApp(ArithOp.Neg, List(term(arg, env)))
    case SList(SSymbol("-") :: args) if args.length >= 2 => Term.ArithApp(ArithOp.Sub, args.map(term(_, env)))
    case SList(SSymbol("+") :: args) => Term.ArithApp(ArithOp.Add, args.map(term(_, env)))
    case SList(SSymbol("*") :: args) => Term.ArithApp(ArithOp.Mul, args.map(term(_, env)))
    case SList(SSymbol("/") :: args) if args.length >= 2 => Term.ArithApp(ArithOp.Div, args.map(term(_, env)))
    case SList(SSymbol("div") :: args) if args.length >= 2 => Term.ArithApp(ArithOp.IntDiv, args.map(term(_, env)))
    case SList(SSymbol("mod") :: a :: b :: Nil) => Term.ArithApp(ArithOp.Mod, List(term(a, env), term(b, env)))
    case SList(SSymbol("abs") :: a :: Nil) => Term.ArithApp(ArithOp.Abs, List(term(a, env)))
    case SList(SSymbol("to_real") :: a :: Nil) => Term.ArithApp(ArithOp.ToReal, List(term(a, env)))
    case SList(SSymbol("to_int") :: a :: Nil) => Term.ArithApp(ArithOp.ToInt, List(term(a, env)))
    case SList(SSymbol("ite") :: cond :: thn :: els :: Nil) =>
      Term.Ite(formula(cond, env), term(thn, env), term(els, env))
    case SList(SSymbol("let") :: SList(bs) :: body :: Nil) =>
      val (bound, inner) = bindings(bs, env)
      Term.Let(bound, term(body, inner))
    case SList(SSymbol("match") :: _) => term(matchToIte(sexpr, env), env)
    case SList(SSymbol("!") :: body :: _) => term(body, env) // an annotated term
    case SList(SSymbol(name) :: args) => application(name, args, env)
    case other => throw Smt2Error(s"not a term: $other")
  end term

  private def application(name: String, args: List[SExpr], env: Map[String, Sort]): Term =
    declared(name, env)
    val concrete = if !env.contains(name) then instance(name, args.map(sortOf(_, env)), None) else name
    Term.App(Term.Const(concrete), args.map(term(_, env)))

  /** Whether `a` is an array: what `select` and `store` accept. */
  private def selectable(a: SExpr, env: Map[String, Sort]): Boolean = sortOf(a, env) match
    case Sort.Array(_, _) => true
    case _ => false

  /** Whether `(as const s)` is the constant array of the theory: `s` an array
   *  sort, and `const` not a symbol of the script's (a constructor `const` of a
   *  parametric datatype is qualified the same way).
   */
  private def constantArray(s: SExpr, env: Map[String, Sort]): Boolean =
    !env.contains("const") && !functions.contains("const") && !macros.contains("const") &&
      !polymorphic.contains("const") && (s match
        case SList(SSymbol("Array") :: _) => true
        case _ => false)

  /** Checks that `name` is declared, bound or a macro. */
  private def declared(name: String, env: Map[String, Sort]): Unit =
    if !env.contains(name) && !functions.contains(name) && !macros.contains(name) && !polymorphic.contains(name) then
      throw Smt2Error(s"unknown symbol $name")

object Parser:
  def parse(input: String): Script = Parser().parse(input)

  /** The reserved words of SMT-LIB and the symbols of its Core theory: a script
   *  cannot declare or define them.
   */
  val reserved: Set[String] = Set(
    "!",
    "_",
    "as",
    "let",
    "exists",
    "forall",
    "match",
    "par",
    "true",
    "false",
    "not",
    "=>",
    "and",
    "or",
    "xor",
    "=",
    "distinct",
    "ite"
  )
