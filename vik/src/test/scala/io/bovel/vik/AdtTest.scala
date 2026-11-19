package io.bovel.vik

import scala.util.Random

import io.bovel.smtlib.{Constructor, Datatype, Sort}
import Formula.*
import Term.*

/** Datatypes: injectivity, distinctness, selectors, testers, exhaustiveness,
 *  acyclicity, finite sorts; and random formulas over finite datatypes against
 *  brute force.
 */
class AdtTest extends munit.FunSuite:
  val list = Datatype(
    "List",
    List(Constructor("nil", Nil), Constructor("cons", List(("head", Sort.Named("U")), ("tail", Sort.Named("List")))))
  )

  def app(f: String, args: Term*): Term = App(Const(f), args.toList)
  def is(c: String, t: Term): Formula = Pred(app(s"(_ is $c)", t))

  def listSolver(): Solver =
    val s = Solver()
    s.declare("U", Nil, "U")
    for c <- List("a", "b", "c") do s.declare(c, Nil, "U")
    for l <- List("l", "m", "n") do s.declare(l, Nil, "List")
    s.declare(list)
    s

  def sat(solver: Solver, formulas: Formula*): Boolean =
    formulas.foreach(solver.assert)
    solver.solve() == solver.Result.Sat

  val (a, b, c, l, m, n) = (Const("a"), Const("b"), Const("c"), Const("l"), Const("m"), Const("n"))
  val nil = Const("nil")

  test("distinctness and injectivity"):
    assert(!sat(listSolver(), nil === app("cons", a, l)))
    assert(!sat(listSolver(), app("cons", a, l) === app("cons", b, m), a !== b))
    assert(!sat(listSolver(), app("cons", a, l) === app("cons", b, m), l !== m))
    assert(sat(listSolver(), app("cons", a, l) === app("cons", b, m), a === b))
    assert(!sat(listSolver(), l === app("cons", a, m), l === app("cons", b, n), Or(List(a !== b, m !== n))))

  test("selectors"):
    assert(!sat(listSolver(), app("head", app("cons", a, l)) !== a))
    assert(!sat(listSolver(), l === app("cons", a, m), app("tail", l) !== m))
    assert(sat(listSolver(), app("head", l) === a, app("head", l) === b)) // l may be nil: head is unconstrained
    assert(!sat(listSolver(), is("cons", l), app("head", l) === a, app("head", l) === b, a !== b))

  test("testers, exhaustiveness and expansion"):
    assert(!sat(listSolver(), Not(is("nil", l)), Not(is("cons", l))))
    assert(!sat(listSolver(), is("nil", l), l === app("cons", a, m)))
    assert(!sat(listSolver(), is("cons", l), l === nil))
    assert(sat(listSolver(), is("cons", l), app("tail", l) === nil))
    assert(!sat(
      listSolver(),
      is("cons", l),
      is("cons", m),
      l !== m,
      app("head", l) === app("head", m),
      app("tail", l) === app("tail", m)
    ))
    assert(!sat(listSolver(), is("nil", l), is("nil", m), l !== m)) // both are nil

  test("acyclicity"):
    assert(!sat(listSolver(), l === app("cons", a, l)))
    assert(!sat(listSolver(), l === app("cons", a, m), m === app("cons", b, l)))
    assert(!sat(listSolver(), is("cons", l), app("tail", l) === l))
    assert(!sat(listSolver(), is("cons", l), is("cons", m), app("tail", l) === m, app("tail", m) === l))
    assert(sat(listSolver(), l === app("cons", a, m), m === app("cons", b, n)))

  test("levels"):
    val s = listSolver()
    s.assert(l === app("cons", a, m))
    assertEquals(s.solve(), s.Result.Sat)
    s.push()
    s.assert(is("nil", l))
    assertEquals(s.solve(), s.Result.Unsat)
    s.pop()
    assertEquals(s.solve(), s.Result.Sat)

  test("finite sorts have finitely many values"):
    val unit = Datatype("Unit", List(Constructor("u", Nil)))
    val option =
      Datatype("Opt", List(Constructor("none", Nil), Constructor("some", List(("value", Sort.Named("Unit"))))))
    def solver(): Solver =
      val s = Solver()
      s.declare(unit)
      s.declare(option)
      for x <- List("x", "y", "z") do s.declare(x, Nil, "Opt")
      s
    val (x, y, z) = (Const("x"), Const("y"), Const("z"))
    assert(sat(solver(), x !== y))
    assert(!sat(solver(), x !== y, y !== z, x !== z)) // only two values: none and some(u)
    assert(!sat(solver(), x !== Const("none"), y !== Const("none"), x !== y))

  test("a field of a finite sort under an infinite sort has finitely many values (issue 125)"):
    // `Val` is infinite through `U`; its `of-Unit` values are one, its `of-Bool` and `of-Opt` values two
    // and three. The tester's expansion invents the fields, which no term of the problem names.
    val unit = Datatype("Unit", List(Constructor("u", Nil)))
    val option =
      Datatype("Opt", List(Constructor("none", Nil), Constructor("some", List(("value", Sort.Bool)))))
    val value = Datatype(
      "Val",
      List(
        Constructor("of-U", List(("to-U", Sort.Named("U")))),
        Constructor("of-Unit", List(("to-Unit", Sort.Named("Unit")))),
        Constructor("of-Bool", List(("to-Bool", Sort.Bool))),
        Constructor("of-Opt", List(("to-Opt", Sort.Named("Opt"))))
      )
    )
    val names = List("x", "y", "z", "w")
    def apart(c: String, n: Int): Boolean =
      val s = Solver()
      s.declare("U", Nil, "U")
      for d <- List(unit, option, value) do s.declare(d)
      for x <- names do s.declare(x, Nil, "Val")
      val some = names.take(n).map(Const(_))
      sat(s, (some.map(is(c, _)) ++ (for (x, i) <- some.zipWithIndex; y <- some.drop(i + 1) yield x !== y))*)
    assert(!apart("of-Unit", 2))
    assert(apart("of-Bool", 2))
    assert(!apart("of-Bool", 3))
    assert(apart("of-Opt", 3))
    assert(!apart("of-Opt", 4))
    assert(apart("of-U", 4))

  /** Random formulas over `Color = red | green | blue` and
   *  `Pair = mk(fst: Color, snd: Color)`, decided by brute force over the 9 × 9
   *  × 3 assignments of two pairs and a color.
   */
  test("random formulas over finite datatypes against brute force"):
    val color = Datatype("Color", List("red", "green", "blue").map(Constructor(_, Nil)))
    val pair =
      Datatype("Pair", List(Constructor("mk", List(("fst", Sort.Named("Color")), ("snd", Sort.Named("Color"))))))
    val colors = List("red", "green", "blue")
    val rnd = Random(9)
    // values: colors as their name, pairs as (fst, snd)
    type Env = Map[String, Any]
    def eval(t: Term, env: Env): Any = t match
      case Const(name) if env.contains(name) => env(name)
      case Const(name) => name // a nullary constructor
      case App(Const("mk"), List(f, s)) => (eval(f, env), eval(s, env))
      case App(Const("fst"), List(p)) => eval(p, env).asInstanceOf[(Any, Any)]._1
      case App(Const("snd"), List(p)) => eval(p, env).asInstanceOf[(Any, Any)]._2
      case _ => throw IllegalArgumentException(t.toString)
    def holds(f: Formula, env: Env): Boolean = f match
      case Eq(l, r) => eval(l, env) == eval(r, env)
      case Pred(App(Const(tester), List(t))) =>
        val v = eval(t, env)
        tester match
          case "(_ is mk)" => v.isInstanceOf[(?, ?)]
          case _ => v == tester.stripPrefix("(_ is ").stripSuffix(")")
      case Not(g) => !holds(g, env)
      case And(gs) => gs.forall(holds(_, env))
      case Or(gs) => gs.exists(holds(_, env))
      case Implies(g, h) => !holds(g, env) || holds(h, env)
      case _ => throw IllegalArgumentException(f.toString)
    def colorTerm(): Term = rnd.nextInt(5) match
      case 0 => Const("c")
      case 1 => app("fst", pairTerm(1))
      case 2 => app("snd", pairTerm(1))
      case _ => Const(colors(rnd.nextInt(3)))
    def pairTerm(depth: Int = 2): Term = rnd.nextInt(if depth > 0 then 3 else 2) match
      case 0 => Const("p")
      case 1 => Const("q")
      case _ => app("mk", colorTerm(), colorTerm())
    def atom(): Formula = rnd.nextInt(5) match
      case 0 => colorTerm() === colorTerm()
      case 1 => pairTerm() === pairTerm()
      case 2 => is(colors(rnd.nextInt(3)), colorTerm())
      case 3 => is("mk", pairTerm())
      case _ => Not(pairTerm() === pairTerm())
    def formula(depth: Int): Formula =
      if depth == 0 then atom()
      else
        rnd.nextInt(4) match
          case 0 => And(List(formula(depth - 1), formula(depth - 1)))
          case 1 => Or(List(formula(depth - 1), formula(depth - 1)))
          case 2 => Not(formula(depth - 1))
          case _ => Implies(formula(depth - 1), formula(depth - 1))
    val pairs = for f <- colors; s <- colors yield (f, s)
    var sats = 0
    for round <- 0 until 200 do
      val f = formula(2 + rnd.nextInt(2))
      val expected = (for p <- pairs; q <- pairs; c <- colors
      yield Map[String, Any]("p" -> p, "q" -> q, "c" -> c)).exists(holds(f, _))
      val s = Solver()
      s.declare(color)
      s.declare(pair)
      s.declare("p", Nil, "Pair")
      s.declare("q", Nil, "Pair")
      s.declare("c", Nil, "Color")
      assertEquals(sat(s, f), expected, s"round $round: $f")
      if expected then sats += 1
    assert(sats > 30 && sats < 170, sats)
