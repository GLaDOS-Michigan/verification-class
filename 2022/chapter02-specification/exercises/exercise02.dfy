//#title IsPrime II
//#desc Working with an implementation proof

// Let's try "implementing" (with a recursive function) a check for
// primeness.

// The definition of IsPrime will be included from exercise01.dfy. Make sure
// that definition is correct before you start implementing it.
include "exercise01.dfy"
//#extract exercise01.template solution exercise01.dfy

// A recursive implementation of IsPrime. The function HasDivisorBelow should
// check if n is divisible by something between 1 and limit (including limit,
// not including 1).
function
  HasDivisorBelow(n:nat, limit:nat): bool
  requires limit >= 1
{
  if limit == 1 then false else
  /*{*/
    true // replace this with an appropriate definition
  /*}*/
}

function
  IsPrime(n: nat): bool {
  if n <= 1 then false else
  !HasDivisorBelow(n, n-1)
}

// You'll now prove IsPrime(n) == IsPrimeSpec(n). This will require a helper
// lemma to deal with the recursion.

// An intermediate spec for what HasDivisorBelow returns. The solution is expressed using an
// exists; you may find it more natural to write a forall.
lemma HasDivisorBelow_ok(n: nat, limit: nat)
  requires 1 <= limit
  /*{*/
  ensures true // replace this with an appropriate postcondition
  /*}*/
{
  /*{*/
  /*}*/
}

lemma IsPrime_ok(n: nat)
  ensures IsPrime(n) == IsPrimeSpec(n)
{
  /*{*/
  // This proof should work if your postcondition for HasDivisorBelow_ok is
  // correct, but you can change it if needed.
  if n <= 2 {
    return;
  }
  HasDivisorBelow_ok(n, n-1);
  /*}*/
}
