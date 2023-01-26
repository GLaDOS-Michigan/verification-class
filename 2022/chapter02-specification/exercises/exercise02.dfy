//#title IsPrime II
//#desc Working with an implementation proof

// Take another little detour to implementation-land by writing a method
// `test_prime` that implements IsPrime with an imperative while() loop.

// The definition of IsPrime will be included from exercise01.dfy. Make sure
// that definition is correct before you start implementing it.
include "exercise01.dfy"
//#extract exercise01.template solution exercise01.dfy

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(candidate:nat) returns (result:bool)
  requires 1<candidate
  ensures result == IsPrime(candidate)
{
/*{*/
  // Fill in the body.
/*}*/
}

method PrimeMain()
{
  var isprime4 := test_prime(4);
/*{*/
/*}*/
  assert !isprime4;
  
  var isprime12 := test_prime(12);
/*{*/
/*}*/
  assert !isprime12;
  
  var isprime44 := test_prime(44);
/*{*/
/*}*/
  assert !isprime44;
}
  

