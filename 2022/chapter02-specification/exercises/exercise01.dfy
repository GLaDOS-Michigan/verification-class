//#title IsPrime I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

/*{*/
/*}*/
predicate IsPrime(candidate:nat)
{
/*{*/
  false  // Replace me
/*}*/
}

lemma ConstantObligations()
  ensures !IsPrime(0)
  ensures !IsPrime(1)
  ensures IsPrime(2)
  ensures IsPrime(3)
  ensures !IsPrime(4)
  ensures !IsPrime(6)
  ensures IsPrime(7)
  ensures !IsPrime(9)
{
/*{*/
/*}*/
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrime(p*66)
{
/*{*/
/*}*/
}



