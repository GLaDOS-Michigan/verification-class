//#title Functions

// A `function` is a mathematical function.
// This one has a domain of the integers and the range is (within) the
// integers. Again, `int` is the entire set of mathematical integers.

// Run dafny on this file. See where it fails. Fix it.

ghost function Double(val:int) : int
{
  // The body of a function is an expression context. No semicolon
  // at the end.
  2 * val
}

// A lemma is like a C++ method or C function (hence the statement context).
// The proof it contains is like a program: a sequence of statements.
// As in C, statements terminate with semicolons and can be grouped into blocks
// with braces.
lemma DoubleIsLikePlus()
{
  assert Double(6) == 6 + 6;
  {
    assert Double(-2) == /*{*/4/*}*/;
  }
}

// A lemma can take arguments. This is one way to prove a statement about
// *any* value, not just a particular literal.
lemma foo4(val:int)
{
  assert Double(val) == val + /*{*/val + val/*}*/;
}
