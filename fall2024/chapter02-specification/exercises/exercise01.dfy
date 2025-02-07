//#title IsPrimeSpec I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

/*{*/
/*}*/
ghost predicate IsPrimeSpec(candidate:nat)
{
  /*{*/
  false  // Replace me
  /*}*/
}

// illustrate IsPrimeSpec on a few examples (note that the verifier is able to
// check these only with some help to find divisors for non-prime numbers)
lemma ConstantObligations()
  ensures !IsPrimeSpec(0)
  ensures !IsPrimeSpec(1)
  ensures IsPrimeSpec(2)
  ensures IsPrimeSpec(3)
  ensures !IsPrimeSpec(4)
  ensures !IsPrimeSpec(6)
  ensures IsPrimeSpec(7)
  ensures !IsPrimeSpec(9)
{
  /*{*/
  /*}*/
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrimeSpec(p*66)
{
  /*{*/
  /*}*/
}


