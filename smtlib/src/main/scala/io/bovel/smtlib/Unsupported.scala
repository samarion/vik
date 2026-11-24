package io.bovel.smtlib

/** Something the solver does not decide: an operation outside a fragment (an
 *  integer multiplication of two unknowns), a sort of a theory it does not
 *  have. The front end's `Smt2Error` is one of these, so a caller that reads
 *  scripts catches the two the same way.
 */
class Unsupported(message: String) extends Exception(message)
