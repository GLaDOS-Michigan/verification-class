//#title Boolean logic

lemma BooleanLogic()
{
  // An assertion is a static check of a boolean expression.
  // This boolean expression is about a boolean implication.
  // Run dafny on this file. See where it fails. Fix it.
  assert true ==> /*{*/ false /*}*/;
}
