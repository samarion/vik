package io.bovel.vik

/** The symbols VIK makes for itself: the constants of the lowering (`.bv!3`,
 *  `.q!7`), its store symbols (`.store!1`), the solver's witnesses of
 *  extensionality (`.witness!0`) and its indices beyond the writes
 *  (`.beyond!0`). Each starts with `.`, which SMT-LIB reserves for the solver,
 *  and the lowering refuses a script's declaration of such a symbol: no script
 *  symbol can be taken for one of these, whatever the order of the declarations
 *  (issues 21, 143 and 158), and nothing has to be checked against the script's
 *  names when one is made.
 */
private[vik] object Names:
  /** Whether a symbol is one of VIK's own. */
  def isOurs(name: String): Boolean = name.startsWith(".")

  /** A constant or a symbol of the lowering's: `.tag!n`. */
  def minted(tag: String, n: Int): String =
    require(tag != witnessTag && tag != beyondTag, s"$tag is the solver's tag")
    s".$tag!$n"

  /** A witness of the solver's: `.witness!n`, a tag the lowering never uses. */
  def witness(n: Int): String = s".$witnessTag!$n"

  /** The solver's index beyond the writes of an index sort (`.beyond!n`), a tag
   *  the lowering never uses.
   */
  def beyond(n: Int): String = s".$beyondTag!$n"

  /** Whether a symbol is the store of an array sort, which the solver's array
   *  lemmas recognize by its name.
   */
  def isStore(name: String): Boolean = name.startsWith(storePrefix)

  /** Whether a symbol is the constant array of an array sort
   *  (`.array.const!n`), a function of the element to the array.
   */
  def isConstArray(name: String): Boolean = name.startsWith(constPrefix)

  /** Whether a symbol is the map of an operator over arrays (`.array.map!n`).
   */
  def isMap(name: String): Boolean = name.startsWith(mapPrefix)

  /** Whether a symbol is one of the array operations the solver's array lemmas
   *  recognize by its name: a store, a constant array or a map.
   */
  def isArrayOperation(name: String): Boolean = isStore(name) || isConstArray(name) || isMap(name)

  private val witnessTag = "witness"
  private val beyondTag = "beyond"
  private val storePrefix = ".store!"
  private val constPrefix = ".array.const!"
  private val mapPrefix = ".array.map!"
