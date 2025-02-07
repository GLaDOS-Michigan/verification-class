//#title Predicates

// A common thing you'll want is a function with a boolean result.
ghost function AtLeastTwiceAsBigFunction(a:int, b:int) : bool
{
  a >= 2*b
}

// It's so fantastically common that there's a shorthand for it: `predicate`.
ghost predicate AtLeastTwiceAsBigPredicate(a:int, b:int)
{
  a >= 2*b
}

ghost function Double(a:int) : int
{
  2 * a
}

lemma TheseTwoPredicatesAreEquivalent(x:int, y:int)
{
  assert AtLeastTwiceAsBigFunction(x, y) == AtLeastTwiceAsBigPredicate(x, y);
}

// Add a 'requires' precondition to make this lemma verify.
// Keep it as simple as possible (e.g. avoid named predicates).
lemma FourTimesIsPrettyBig(x:int)
/*{*/
/*}*/
{
  assert AtLeastTwiceAsBigPredicate(Double(Double(x)), x);
}

