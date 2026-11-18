package io.bovel.vik

import io.bovel.smtlib.*
import io.bovel.smtlib.Formula.*
import io.bovel.smtlib.Term.*

/** Datatype declarations: parsed, represented, printed; refused at `check-sat`
 *  until the theory exists.
 */
class DatatypesTest extends munit.FunSuite:
  val list =
    Datatype(
      "List",
      List(Constructor("nil", Nil), Constructor("cons", List(("head", Sort.Int), ("tail", Sort.Named("List")))))
    )

  test("declare-datatype and declare-datatypes"):
    val single = Parser.parse("(declare-datatype List ((nil) (cons (head Int) (tail List))))")
    val plural = Parser.parse("(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))")
    assertEquals(single.commands, List(Command.DeclareDatatypes(List(list))))
    assertEquals(plural.commands, single.commands)
    // A parametric declaration declares nothing by itself: its instances do, on first use, as datatypes
    // named as written with their own constructors.
    val parametric = Parser.parse("""
      (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
      (declare-const l (List Int))""")
    val intList = Datatype(
      "(List Int)",
      List(
        Constructor("nil@Int", Nil),
        Constructor("cons@Int", List(("head@Int", Sort.Int), ("tail@Int", Sort.Named("(List Int)"))))
      )
    )
    assertEquals(
      parametric.commands,
      List(Command.DeclareDatatypes(List(intList)), Command.DeclareFun("l", Nil, Sort.Named("(List Int)")))
    )

  test("constructors, selectors and testers as terms"):
    val script = Parser.parse("""
      (declare-datatype List ((nil) (cons (head Int) (tail List))))
      (declare-const l List)
      (assert (= l (cons 1 nil)))
      (assert (= (head l) 1))
      (assert ((_ is cons) l))
      (assert (not ((_ is nil) (tail l))))""")
    val asserts = script.commands.collect { case Command.Assert(f) => f }
    val l = Const("l")
    assertEquals(asserts(0), Eq(List(l, App(Const("cons"), List(Numeral(1), Const("nil"))))))
    assertEquals(asserts(1), Eq(List(App(Const("head"), List(l)), Numeral(1))))
    assertEquals(asserts(2), IsConstructor("cons", l))
    assertEquals(asserts(3), Not(IsConstructor("nil", App(Const("tail"), List(l)))))
    assertEquals(Parser.parse(Printer.print(script)), script)
    assert(Printer.print(script).contains("(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))"))
    assert(Printer.print(script).contains("((_ is cons) l)"))

  test("scripts with datatypes are decided"):
    val decls =
      "(declare-sort U 0) (declare-datatype List ((nil) (cons (head U) (tail List)))) (declare-const l List) (declare-const m List) (declare-const a U) (declare-const b U)"
    def play(script: String) = Session.run(Parser.parse(s"$decls $script (check-sat)"))
    assertEquals(play("(assert (= l (cons a m))) (assert ((_ is nil) l))"), List("unsat"))
    assertEquals(play("(assert (= l (cons a m))) (assert (= (head l) b)) (assert (distinct a b))"), List("unsat"))
    assertEquals(play("(assert (= l (cons a m))) (assert (= (tail l) l))"), List("unsat"))
    assertEquals(play("(assert (= l (cons a m))) (assert ((_ is cons) l)) (assert (= (head l) a))"), List("sat"))
    assertEquals(play("(assert (not ((_ is nil) l))) (assert (not ((_ is cons) l)))"), List("unsat"))
    // Int fields: the datatype rules and the LIA solver combined
    assertEquals(
      Session.run(Parser.parse(
        "(declare-datatype L ((nil) (cons (head Int) (tail L)))) (declare-const l L) (assert (= l (cons 3 nil))) (assert (< (head l) 2)) (check-sat)"
      )),
      List("unsat")
    )

  test("an array field is read over the writes to it") {
    // The field's sort is the sort of the stores written to it, or a read
    // through the selector got no read-over-write lemma, and this was sat.
    assertEquals(
      Session.run(Parser.parse(
        """(declare-datatypes ((arr 0)) (((mk (data (Array Int Bool))))))
          |(declare-fun d () arr) (declare-fun i () Int) (declare-fun j () Int) (declare-fun v () Bool)
          |(assert (not (= i j)))
          |(assert (not (= (select (data (mk (store (data d) i v))) j) (select (data d) j))))
          |(check-sat)""".stripMargin
      )),
      List("unsat")
    )
  }

  test("an array field read through its selector is the constructor's array"):
    // The e-graph equates `(arr (C a))` with `a`, but the two were never a pair of arrays to share, so
    // their reads stayed two unrelated integers for the arithmetic solver, and these were sat (issue 134).
    def run(text: String) = Session.run(Parser.parse(s"""
      (declare-datatype D ((C (arr (Array Int Int)))))
      (declare-const a (Array Int Int)) (declare-const b (Array Int Int)) (declare-const x D)
      (declare-const i Int) (declare-const j Int)
      $text
      (check-sat)"""))
    assertEquals(run("(assert (not (= (select (arr (C a)) 0) (select a 0))))"), List("unsat"))
    assertEquals(run("(assert (= x (C a))) (assert (< (select (arr x) 0) (select a 0)))"), List("unsat"))
    assertEquals(
      run("(assert (<= i j)) (assert (<= j i)) (assert (not (= (select (arr (C a)) i) (select a j))))"),
      List("unsat")
    )
    assertEquals(run("(assert (not (= (select (arr (C a)) 0) (select b 0))))"), List("sat"))
