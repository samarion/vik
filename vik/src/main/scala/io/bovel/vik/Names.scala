package io.bovel.vik

/** The symbols VIK makes for itself: the constants of the lowering (`.bv!3`,
 *  `.q!7`), its store symbols (`.store!1`), the solver's witnesses of
 *  extensionality (`.witness!0`). Each starts with `.`, which SMT-LIB reserves
 *  for the solver, and the lowering refuses a script's declaration of such a
 *  symbol: no script symbol can be taken for one of these, whatever the order
 *  of the declarations (issues 21, 143 and 158), and nothing has to be checked
 *  against the script's names when one is made.
 */
private[vik] object Names:
  /** Whether a symbol is one of VIK's own. */
  def isOurs(name: String): Boolean = name.startsWith(".")

  /** A constant or a symbol of the lowering's: `.tag!n`. */
  def minted(tag: String, n: Int): String =
    require(tag != witnessTag, s"$witnessTag is the solver's tag")
    s".$tag!$n"

  /** A witness of the solver's: `.witness!n`, a tag the lowering never uses. */
  def witness(n: Int): String = s".$witnessTag!$n"

  /** Whether a symbol is the store of an array sort, which the solver's array
   *  lemmas recognize by its name.
   */
  def isStore(name: String): Boolean = name.startsWith(storePrefix)

  /** Whether `name` is one of the solver's witnesses ([[witness]]). */
  def isWitness(name: String): Boolean = name.startsWith(s".$witnessTag!")

  /** The `n` of the witness `.witness!n` ([[witness]]). */
  def witnessIndex(name: String): Option[Int] =
    if isWitness(name) then name.drop(witnessTag.length + 2).toIntOption else None

  private val witnessTag = "witness"
  private val storePrefix = ".store!"
