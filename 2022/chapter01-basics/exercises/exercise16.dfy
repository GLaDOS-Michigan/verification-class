//#title IsEven
//#desc Hoare logic

// So far, we have introduced function and datatype definitions;
// the definition of each is entirely visible to its users.
// We have also discussed lemmas. The body of a lemma is invisible
// to its callers -- but we haven't ever called a lemma!
// Calling lemmas is how we can compose proofs to prove larger concepts.

ghost predicate IsEven(x:int)
{
  x/2*2==x
}

// A lemma is like a C function; it can return values. Let's return a value
// and then ensure a property of it.
lemma ExplainEvenNumbers(x:int) returns (twocount:int)
  // This lemma doesn't work unless we know x is even.
  // This requires clause is a fact we get to assume inside the lemma.
  requires IsEven(x)
// To export knowledge from a lemma, we declare it in an `ensures` clause.
  ensures twocount*2 == x
{
  // return twocount by assigning it.
  twocount := x / /*{*/3/*}*/;
}

ghost predicate AlternateEven(x:int)
{
  exists twocount :: twocount * 2 == x
}

// Instead of hiding the thing we prove inside the body as an assert,
// let's export it.
lemma EvenDefinitionsAreEquivalent(x:int)
  ensures IsEven(x) == AlternateEven(x)
{
  // Wow, that proved without us providing a witness!
}

