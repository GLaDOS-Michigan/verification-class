//#title More set tools

// <= on sets is subset.
predicate HasFourFiveSix(intset:set<int>)
{
  {6,5,4} <= intset  // I can because they're sets!
}

lemma SomeAssertionsAboutSets()
{
  assert !HasFourFiveSix({1,2,4,6,7});

  // This is just a mathematical "let" statement.
  // It's safe to substitute the value wherever "happySet" appears.
  var happySet := {1,2,4,6,7,5};
  assert HasFourFiveSix(happySet);

  // - on sets is difference.
  assert happySet - {4,5,6} == {7,2,1};

  // + on sets is union.
  assert HasFourFiveSix({4,6} + {5});

  // |x| on a set is cardinality.
  // (set<T> is always finite; there is another type iset<T> for
  // possibly-infinite sets.)
  assert |happySet| == /*{*/7/*}*/;
}
