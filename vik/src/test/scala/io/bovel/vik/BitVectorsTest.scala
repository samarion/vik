package io.bovel.vik

import scala.util.Random

import io.bovel.smtlib.Parser

/** The lowering of bit-vector arithmetic to integers: hand cases, and random
 *  4-bit expressions whose value under an assignment is computed directly and
 *  compared with what the solver accepts.
 */
class BitVectorsTest extends munit.FunSuite:
  def sat(script: String): Boolean = Session.answers(Parser.parse(script)) == List(Some(true))

  val decls = "(set-logic QF_BV) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))"

  test("get-assertions shows the lowered stack"):
    val out = Session.run(Parser.parse(s"$decls (assert (bvult x y)) (get-assertions)"))
    // `bvult`, lowered, and nothing else: the range of a bit-vector is its sort's, not an assertion.
    assertEquals(out.last, "((<= (+ x 1) y))")

  test("overflow, comparisons, extraction"):
    assert(sat(s"$decls (assert (= (bvadd x #xFF) #x00)) (assert (= x #x01)) (check-sat)"))
    assert(!sat(s"$decls (assert (= x #xFF)) (assert (bvult x (bvadd x #x01))) (check-sat)"))
    assert(sat(s"$decls (assert (= x #xFE)) (assert (bvult x (bvadd x #x01))) (check-sat)"))
    assert(
      sat(s"$decls (assert (bvslt x #x00)) (assert (bvugt x #x7F)) (check-sat)")
    ) // negative signed = high unsigned
    assert(!sat(s"$decls (assert (bvslt x #x00)) (assert (bvult x #x80)) (check-sat)"))
    assert(sat(
      s"$decls (assert (= ((_ extract 7 4) x) #x3)) (assert (= ((_ extract 3 0) x) #xA)) (assert (= x #x3A)) (check-sat)"
    ))
    assert(!sat(s"$decls (assert (= ((_ extract 7 4) x) #x3)) (assert (= x #x2A)) (check-sat)"))
    assert(
      sat(s"$decls (assert (= (concat ((_ extract 7 4) x) ((_ extract 3 0) x)) x)) (assert (= x #xC7)) (check-sat)")
    )
    assert(sat(s"$decls (assert (= (bvmul x #x03) #x01)) (check-sat)")) // 3 × 171 = 513 = 1 mod 256
    assert(!sat(s"$decls (assert (= (bvmul x #x02) #x01)) (check-sat)"))
    assert(sat(s"$decls (assert (= ((_ sign_extend 8) x) (_ bv65535 16))) (assert (= x #xFF)) (check-sat)"))
    assert(
      sat(s"$decls (assert (= (bvudiv x #x03) #x05)) (assert (= (bvurem x #x03) #x02)) (assert (= x #x11)) (check-sat)")
    )
    assert(
      sat(s"$decls (assert (= (bvand x #x0F) #x07)) (assert (= (bvlshr x #x04) #x0A)) (assert (= x #xA7)) (check-sat)")
    )
    assert(sat(s"$decls (assert (= (bvnot x) (bvneg (bvadd x #x01)))) (check-sat)")) // an identity: sat for every x
    // Signed divisions by a constant: -7 / 2 = -3, -7 rem 2 = -1, -7 mod 2 = 1, -7 / -2 = 3, 7 / -2 = -3, 7 mod -2 = -1
    assert(
      sat(s"$decls (assert (= x #xF9)) (assert (= (bvsdiv x #x02) #xFD)) (assert (= (bvsrem x #x02) #xFF)) (check-sat)")
    )
    assert(
      sat(s"$decls (assert (= x #xF9)) (assert (= (bvsmod x #x02) #x01)) (assert (= (bvsdiv x #xFE) #x03)) (check-sat)")
    )
    assert(
      sat(s"$decls (assert (= x #x07)) (assert (= (bvsdiv x #xFE) #xFD)) (assert (= (bvsmod x #xFE) #xFF)) (check-sat)")
    )
    assert(!sat(s"$decls (assert (= x #xF9)) (assert (= (bvsdiv x #x02) #xFC)) (check-sat)")) // not the floor
    assert(
      sat(s"$decls (assert (= x #x80)) (assert (= (bvsdiv x #xFF) #x80)) (assert (= (bvashr x #x03) #xF0)) (check-sat)")
    )
    assert(sat(
      s"$decls (assert (bvslt x #x00)) (assert (= (bvsdiv x #x00) #x01)) (assert (= (bvsrem x #x00) x)) (check-sat)"
    ))
    assert(sat(
      s"$decls (assert (bvsge x #x00)) (assert (= (bvsdiv x #x00) #xFF)) (assert (= (bvsmod x #x00) x)) (check-sat)"
    ))
    assert(!sat(s"$decls (assert (distinct (bvnot x) (bvneg (bvadd x #x01)))) (check-sat)"))
    // An unknown divisor: the division is exact, and its quotient and remainder are the only pair.
    assert(sat(s"$decls (assert (= (bvudiv x y) #x0a)) (assert (= (bvurem x y) #x02)) (assert (= y #x07)) (check-sat)"))
    assert(!sat(
      s"$decls (assert (= (bvudiv x y) #x0a)) (assert (= (bvurem x y) #x02)) (assert (= y #x07))" +
        " (assert (distinct x #x48)) (check-sat)"
    ))
    assert(!sat(s"$decls (assert (bvugt y #x00)) (assert (bvuge (bvurem x y) y)) (check-sat)"))

  /** A random 4-bit expression over `x` and `y` as SMT-LIB text, with its value
   *  under `x = vx`, `y = vy`.
   */
  def expression(rnd: Random, depth: Int, vx: Int, vy: Int): (String, Int) =
    def lit(v: Int) = f"#x$v%x"
    if depth == 0 then
      rnd.nextInt(3) match
        case 0 => ("x", vx)
        case 1 => ("y", vy)
        case _ =>
          val v = rnd.nextInt(16)
          (lit(v), v)
    else
      val (a, va) = expression(rnd, depth - 1, vx, vy)
      val (b, vb) = expression(rnd, depth - 1, vx, vy)
      val c = rnd.nextInt(16)
      def signed(v: Int) = if v >= 8 then v - 16 else v
      val (sa, sc) = (signed(va), signed(c))
      rnd.nextInt(15) match
        case 11 => (s"(bvsdiv $a ${lit(c)})", (if sc == 0 then (if sa >= 0 then -1 else 1) else sa / sc) & 15)
        case 12 => (s"(bvsrem $a ${lit(c)})", (if sc == 0 then sa else sa % sc) & 15)
        case 13 => (s"(bvsmod $a ${lit(c)})", (if sc == 0 then sa else Math.floorMod(sa, sc)) & 15)
        case 14 => (s"(bvashr $a ${lit(c % 5)})", (sa >> (c % 5)) & 15)
        case 0 => (s"(bvadd $a $b)", (va + vb) & 15)
        case 1 => (s"(bvsub $a $b)", (va - vb) & 15)
        case 2 => (s"(bvneg $a)", (-va) & 15)
        case 3 => (s"(bvnot $a)", (~va) & 15)
        case 4 => (s"(bvmul $a ${lit(c)})", (va * c) & 15)
        case 5 => (s"(bvshl $a ${lit(c % 5)})", (va << (c % 5)) & 15)
        case 6 => (s"(bvlshr $a ${lit(c % 5)})", va >>> (c % 5))
        case 7 => (s"(bvudiv $a ${lit(c)})", if c == 0 then 15 else va / c)
        case 8 => (s"(bvurem $a ${lit(c)})", if c == 0 then va else va % c)
        case 9 =>
          val i = rnd.nextInt(4)
          val j = rnd.nextInt(i + 1)
          (s"((_ zero_extend ${3 - i + j}) ((_ extract $i $j) $a))", (va >>> j) & ((1 << (i - j + 1)) - 1))
        case _ =>
          val mask = List(0, 1, 3, 7, 15, 14, 12, 8)(rnd.nextInt(8))
          (s"(bvand $a ${lit(mask)})", va & mask)
  end expression

  test("random 4-bit expressions against direct evaluation"):
    val rnd = Random(5)
    for round <- 0 until 150 do
      val vx = rnd.nextInt(16)
      val vy = rnd.nextInt(16)
      val (e, v) = expression(rnd, 2, vx, vy)
      val wrong = (v + 1 + rnd.nextInt(15)) & 15
      def script(value: Int) =
        f"(declare-const x (_ BitVec 4)) (declare-const y (_ BitVec 4)) (assert (= x #x$vx%x)) (assert (= y #x$vy%x)) (assert (= $e #x$value%x)) (check-sat)"
      assert(sat(script(v)), s"round $round: $e should be ${v} under x = $vx, y = $vy")
      assert(!sat(script(wrong)), s"round $round: $e is not $wrong under x = $vx, y = $vy")

  test("signed comparisons against direct evaluation"):
    val rnd = Random(6)
    for round <- 0 until 60 do
      val vx = rnd.nextInt(16)
      val vy = rnd.nextInt(16)
      def signed(v: Int) = if v >= 8 then v - 16 else v
      val ops = List(
        ("bvslt", signed(vx) < signed(vy)),
        ("bvsle", signed(vx) <= signed(vy)),
        ("bvsgt", signed(vx) > signed(vy)),
        ("bvsge", signed(vx) >= signed(vy)),
        ("bvult", vx < vy),
        ("bvuge", vx >= vy)
      )
      val (op, expected) = ops(rnd.nextInt(ops.length))
      val s =
        f"(declare-const x (_ BitVec 4)) (declare-const y (_ BitVec 4)) (assert (= x #x$vx%x)) (assert (= y #x$vy%x)) (assert ($op x y)) (check-sat)"
      assertEquals(sat(s), expected, s"round $round: $op $vx $vy")
