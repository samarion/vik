package io.bovel.smtlib

import scala.util.hashing.MurmurHash3

/** A term of the surface language, as SMT-LIB writes it: applications are n-ary
 *  where the standard's `:left-assoc` makes them so, binders carry their
 *  parameter names, and nothing is rewritten — the solver's `Lowering` turns
 *  these into its own trees. An operation outside the solver's fragment (a
 *  `bvor` of two unknowns, an integer division) parses fine; the lowering is
 *  where the fragment line is drawn, with a message.
 */
enum Term:
  /** A declared symbol, or a name bound by an enclosing `let`. */
  case Const(name: String)
  case Numeral(value: BigInt)

  /** A decimal literal `d.f`, kept as written: `unscaled × 10^(-scale)`. */
  case Decimal(unscaled: BigInt, scale: Int)

  /** A bit-vector literal of `width` bits (`#b...`, `#x...`, `(_ bvN w)`), its
   *  value in `[0, 2^width)`.
   */
  case Bits(value: BigInt, width: Int)

  /** An uninterpreted application. */
  case App(fun: Term, args: List[Term])
  case ArithApp(op: ArithOp, args: List[Term])
  case BvApp(op: BvOp, args: List[Term])
  case Select(array: Term, index: Term)
  case Store(array: Term, index: Term, value: Term)

  /** The array of `sort` holding `value` at every index:
   *  `((as const sort) value)`.
   */
  case ConstArray(sort: Sort, value: Term)
  case Ite(cond: Formula, thn: Term, els: Term)
  case Let(bindings: List[(String, Term | Formula)], body: Term)

  /** A formula where a term is expected: a `Bool`-sorted argument, body or
   *  field.
   */
  case Bool(formula: Formula)

  private lazy val hash: Int = MurmurHash3.caseClassHash(this)
  override def hashCode: Int = hash
  override def toString: String = Printer.print(this)

/** The arithmetic operations of Ints and Reals — shared symbols, an
 *  occurrence's sort is a fact about its arguments. `Div` is the reals' `/`;
 *  `IntDiv`, `Mod` and `Abs` are the integers'.
 */
enum ArithOp(val name: String):
  case Add extends ArithOp("+")
  case Sub extends ArithOp("-")
  case Neg extends ArithOp("-")
  case Mul extends ArithOp("*")
  case Div extends ArithOp("/")
  case IntDiv extends ArithOp("div")
  case Mod extends ArithOp("mod")
  case Abs extends ArithOp("abs")
  case ToReal extends ArithOp("to_real")
  case ToInt extends ArithOp("to_int")

/** The operations of FixedSizeBitVectors, the whole signature: what the
 *  solver's fragment excludes is rejected by the lowering, not the parser.
 */
enum BvOp(val name: String):
  case Add extends BvOp("bvadd")
  case Sub extends BvOp("bvsub")
  case Neg extends BvOp("bvneg")
  case Not extends BvOp("bvnot")
  case Mul extends BvOp("bvmul")
  case And extends BvOp("bvand")
  case Or extends BvOp("bvor")
  case Nand extends BvOp("bvnand")
  case Nor extends BvOp("bvnor")
  case Xor extends BvOp("bvxor")
  case Xnor extends BvOp("bvxnor")
  case Comp extends BvOp("bvcomp")
  case Shl extends BvOp("bvshl")
  case Lshr extends BvOp("bvlshr")
  case Ashr extends BvOp("bvashr")
  case Udiv extends BvOp("bvudiv")
  case Sdiv extends BvOp("bvsdiv")
  case Urem extends BvOp("bvurem")
  case Srem extends BvOp("bvsrem")
  case Smod extends BvOp("bvsmod")
  case Concat extends BvOp("concat")
  case UbvToInt extends BvOp("ubv_to_int")
  case SbvToInt extends BvOp("sbv_to_int")
  case Extract(i: Int, j: Int) extends BvOp("extract")
  case ZeroExtend(k: Int) extends BvOp("zero_extend")
  case SignExtend(k: Int) extends BvOp("sign_extend")
  case IntToBv(n: Int) extends BvOp("int_to_bv")
  case Repeat(k: Int) extends BvOp("repeat")
  case RotateLeft(k: Int) extends BvOp("rotate_left")
  case RotateRight(k: Int) extends BvOp("rotate_right")

  /** The `(_ name i j)` indices, empty for the plain operations. */
  def indices: List[Int] = this match
    case Extract(i, j) => List(i, j)
    case IntToBv(n) => List(n)
    case ZeroExtend(k) => List(k)
    case SignExtend(k) => List(k)
    case Repeat(k) => List(k)
    case RotateLeft(k) => List(k)
    case RotateRight(k) => List(k)
    case _ => Nil

object BvOp:
  /** The plain (unindexed) operations by name. */
  val named: Map[String, BvOp] =
    List(
      Add,
      Sub,
      Neg,
      Not,
      Mul,
      And,
      Or,
      Nand,
      Nor,
      Xor,
      Xnor,
      Comp,
      Shl,
      Lshr,
      Ashr,
      Udiv,
      Sdiv,
      Urem,
      Smod,
      Srem,
      Concat,
      UbvToInt,
      SbvToInt
    ).map(op => op.name -> op).toMap
      ++ Map("bv2nat" -> UbvToInt, "bv2int" -> SbvToInt) // the names before SMT-LIB 2.7's renaming

  /** An indexed operation `(_ name k...)`, `None` for other identifiers. */
  def indexed(name: String, indices: List[Int]): Option[BvOp] = (name, indices) match
    case ("extract", List(i, j)) => Some(Extract(i, j))
    case ("int_to_bv" | "int2bv", List(n)) => Some(IntToBv(n)) // int2bv: the name before the renaming
    case ("zero_extend", List(k)) => Some(ZeroExtend(k))
    case ("sign_extend", List(k)) => Some(SignExtend(k))
    case ("repeat", List(k)) => Some(Repeat(k))
    case ("rotate_left", List(k)) => Some(RotateLeft(k))
    case ("rotate_right", List(k)) => Some(RotateRight(k))
    case _ => None

enum CmpOp(val name: String):
  case Le extends CmpOp("<=")
  case Lt extends CmpOp("<")
  case Ge extends CmpOp(">=")
  case Gt extends CmpOp(">")

enum BvCmpOp(val name: String):
  case Ult extends BvCmpOp("bvult")
  case Ule extends BvCmpOp("bvule")
  case Ugt extends BvCmpOp("bvugt")
  case Uge extends BvCmpOp("bvuge")
  case Slt extends BvCmpOp("bvslt")
  case Sle extends BvCmpOp("bvsle")
  case Sgt extends BvCmpOp("bvsgt")
  case Sge extends BvCmpOp("bvsge")

  /** Whether the comparison reads its operands as signed. */
  def signed: Boolean = this match
    case Slt | Sle | Sgt | Sge => true
    case _ => false

object BvCmpOp:
  val named: Map[String, BvCmpOp] = BvCmpOp.values.map(op => op.name -> op).toMap

/** A formula of the surface language: the connectives, the chainable atoms as
 *  written (`(= a b c)`, `(< a b c)` stay n-ary), `let` and term-level names as
 *  SMT-LIB has them.
 */
enum Formula:
  case True
  case False
  case Not(arg: Formula)
  case And(args: List[Formula])
  case Or(args: List[Formula])

  /** `(=> a b c)`: right-associative, as the standard declares it. */
  case Implies(args: List[Formula])

  /** `(xor a b c)`: left-associative. */
  case Xor(args: List[Formula])

  /** `(= p q r)` on Booleans: chained equivalence. */
  case Iff(args: List[Formula])

  /** `(= a b c)` on terms: chained. */
  case Eq(args: List[Term])
  case Distinct(args: List[Term])

  /** `(<= a b c)`, `(< ...)`, `(>= ...)`, `(> ...)`: chained. */
  case Cmp(op: CmpOp, args: List[Term])
  case BvCmp(op: BvCmpOp, lhs: Term, rhs: Term)
  case Ite(cond: Formula, thn: Formula, els: Formula)

  /** `((_ is C) t)`: the tester of constructor `C`. */
  case IsConstructor(constructor: String, arg: Term)

  /** `(is_int r)`: whether the real `r` is an integer (Reals_Ints). */
  case IsInt(arg: Term)
  case Let(bindings: List[(String, Term | Formula)], body: Formula)

  /** A `Bool`-sorted term where a formula is expected: a constant, an
   *  application.
   */
  case Pred(term: Term)

  private lazy val hash: Int = MurmurHash3.caseClassHash(this)
  override def hashCode: Int = hash
  override def toString: String = Printer.print(this)
