package io.bovel.smtlib

import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration

/** The scripts the parser once did not come back from. Each is read in a thread
 *  of its own under a wall-clock limit, so that a regression fails here instead
 *  of hanging the run: that is why these tests are not in `ParserTest`, which
 *  also runs on Scala.js and Scala Native, where nothing can stop a loop.
 */
class ParserEndsTest extends munit.FunSuite:
  private def parse(text: String): Script = Await.result(Future(Parser.parse(text)), Duration(10, "s"))

  /** The selectors' sorts of the datatype `name`, as declared. */
  private def fields(script: Script, name: String): List[Sort] =
    script.commands.collect { case Command.DeclareDatatypes(datatypes) => datatypes }.flatten
      .find(_.name == name).get.constructors.flatMap(_.selectors.map(_._2))

  test("a define-sort cannot lead back to itself"):
    // The name was visible in its own body, which expanded without end at the first use (issue 177).
    for script <- List(
        "(define-sort S () S) (declare-const x S)",
        "(define-sort S () (Array Int S)) (declare-const x S)",
        "(declare-datatype Option (par (X) ((none) (some (val X))))) (define-sort M (X) (M (Option X)))" +
          "(declare-const x (M Int))",
        // Through another definition, made first with a name that did not exist yet.
        "(define-sort A () B) (define-sort B () A) (declare-const x A)",
        "(define-sort A (X) (Array X B)) (define-sort B () (A Int)) (declare-const x B)"
      )
    do
      val e = intercept[Smt2Error](parse(script))
      assert(e.getMessage.contains("in its own definition"), e.getMessage)
    // A parameter named like the sort is the parameter, and definitions may build on earlier ones.
    parse("(define-sort T (T) (Array T Int)) (declare-const x (T Int))")
    parse("(define-sort P (X) (Array X X)) (define-sort Q (Y) (P (P Y))) (declare-const x (Q Int))")
    parse("(define-sort A () Int) (define-sort B () (Array A A)) (declare-const x B)")

  test("a sort parameter may be named like a sort of the script"):
    // The parameter `T` bound to the sort `T` was read as the parameter again, without end (issue 152).
    val list = "(declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (head T) (tail (Lst T)))))))"
    val after = parse(s"$list (declare-sort T 0) (declare-const a (Lst T)) (assert ((_ is cons) a))")
    assertEquals(fields(after, "(Lst T)"), List(Sort.Named("T"), Sort.Named("(Lst T)")))
    // In the declaration `T` is the parameter, also when the sort was there first: the parameter shadows it.
    val before = parse(s"""
      (declare-sort T 0) $list
      (declare-const a (Lst T)) (declare-const b (Lst Int)) (declare-const t T)
      (assert (= a (cons t (as nil (Lst T))))) (assert (= (head b) 1))""")
    assertEquals(fields(before, "(Lst T)"), List(Sort.Named("T"), Sort.Named("(Lst T)")))
    assertEquals(fields(before, "(Lst Int)"), List(Sort.Int, Sort.Named("(Lst Int)")))
    // The same for a declared sort parameter, at the instance of a function.
    val function = parse(
      "(declare-sort X 0) (declare-const a X) (declare-sort-parameter X) (declare-fun f (X) X) (assert (= (f a) a))"
    )
    assert(function.commands.contains(Command.DeclareFun("f@X", List(Sort.Named("X")), Sort.Named("X"))))

  test("a non-regular parametric datatype is refused"):
    // Each instance needs one of the same datatype at a larger sort, and the parser made them without end (issue 151).
    val option = "(declare-datatype Option (par (X) ((none) (some (val X)))))"
    for script <- List(
        """(declare-datatype Pair (par (A B) ((pair (fst A) (snd B)))))
           (declare-datatype N (par (T) ((nnil) (ncons (h T) (t (N (Pair T T)))))))
           (declare-const x (N Int))""",
        s"""$option
           (declare-datatype N (par (X) ((nil) (cons (hd X) (tl (N (Option X)))))))
           (declare-const x (N Int))""",
        // Through another datatype of the group, through an instance, behind a `define-sort`, and with the
        // parameters swapped, where the larger sort comes back to its place a step later.
        s"""$option
           (declare-datatypes ((A 1) (B 1)) ((par (X) ((a0) (a1 (f (B (Option X)))))) (par (Y) ((b1 (g (A Y)))))))
           (declare-const x (A Int))""",
        s"""$option
           (declare-datatype N (par (X) ((n0) (n1 (f (Option (N (Option X))))))))
           (declare-const x (N Int))""",
        s"""$option (define-sort Maybe (X) (Option X))
           (declare-datatype N (par (X) ((n0) (n1 (f (N (Maybe X)))))))
           (declare-const x (N Int))""",
        s"""$option
           (declare-datatype S (par (X Y) ((s0) (s1 (f (S (Option Y) X))))))
           (declare-const x (S Int Bool))""",
        // A regular datatype with a field at an instance of a non-regular one.
        s"""$option
           (declare-datatype N (par (X) ((nil) (cons (hd X) (tl (N (Option X)))))))
           (declare-datatype R (par (X) ((r (rx X) (f (N Int))))))
           (declare-const x (R Bool))"""
      )
    do
      val e = intercept[Smt2Error](parse(script))
      assert(e.getMessage.contains("a non-regular datatype"), e.getMessage)
    val e = intercept[Smt2Error](parse(
      s"$option (declare-datatype N (par (X) ((nil) (cons (hd X) (tl (N (Option X))))))) (declare-const x (N Int))"
    ))
    assertEquals(
      e.getMessage,
      "N: a non-regular datatype, which needs itself at ever larger sorts, is not supported"
    )
    // Regular ones: an instance in an instance, the parameters swapped, instances at sorts written in full
    // (cvc5's `dt-regular-nested-param`), and all of them at sorts that contain one another.
    parse(s"""$option
      (declare-datatype List (par (X) ((nil) (cons (head X) (tail (List X))))))
      (declare-datatype Rose (par (X) ((rose (label X) (subtrees (List (Rose X)))))))
      (declare-datatype Swap (par (X Y) ((leaf) (swap (x X) (rest (Swap Y X))))))
      (declare-datatype D (par (X) ((d0 (dx X)) (d1 (df (D (Option Int)))) (d2 (dh (D (Option (Option Int))))))))
      (declare-datatypes ((P 2) (Q 1)) (
        (par (X Y) ((p0) (p1 (p1a (P Y X)) (p1b (Q X)) (p1d (Q (Option Int))))))
        (par (Z) ((q0) (q1 (q1a (Q Z)) (q1b (Option Z)) (q1c (P Z Int)))))))
      (declare-datatype Shift (par (X Y) ((s0) (s1 (sf (Shift Int (Option X)))))))
      (declare-const a (Rose (List (Option Int))))
      (declare-const b (List (List (List Int))))
      (declare-const c (Swap Int (Option Int)))
      (declare-const d (D Int))
      (declare-const e (P Bool Int))
      (declare-const f (Shift Bool Bool))
      """)
