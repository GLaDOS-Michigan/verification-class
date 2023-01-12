//#title Quantifiers
include "LunchLibrary.dfy"
include "DirectionsLibrary.dfy"

// Most of what we'll be working with in proof are quantified
// statements: for all inputs, my program produces the right output!
lemma Forall()
{
  assert forall x:int :: x+x == 2*x;
}

// Remember this critter from exercise12? We can rewrite it in a forall.
lemma AnotherForall()
{
  // "Two wrongs don't make a right, but ..."
  assert forall dir :: TurnLeft(/*{*/TurnLeft(TurnLeft(dir))/*}*/) == TurnRight(TurnRight(dir));
}

// Here's there-exists, forall's evil twin.
// exists x :: P(x) == !forall x :: !P(x)
lemma TryThatCheeseOnASandwich()
{
  // Hey, neat. Dafny has a hard time proving exists. It needs
  // a "witness".
  // To proceed, replace 'false' with 'true', and move on to the
  // next lemma to read about how to solve it.
  // If the '?' syntax is surprising, go re-read DirectionsLibrary.dfy.
  assert (forall o1:Order :: o1.Appetizer?
    ==> exists o2:Order :: o2.Sandwich? && o1.cheese == o2.cheese)
    || /*{*/ false /*}*/;
}

lemma CheeseTakeTwo()
{
  // So here's the "statement" version of a forall expression.
  // With nothing in the body, it's exactly equivalent to the assertion
  // above.
  forall o1:Order
    // The assumptions follow a '|' ("such that")
    | o1.Appetizer?
    // The conclusions follow a "requires" keyword.
    ensures exists o2:Order :: o2.Sandwich? && o1.cheese == o2.cheese
  {
    // The body of the forall statement is a proof context for the
    // statement's conclusion. Inside here, o1 is defined, and we
    // can use it to complete the proof.

    // But how? What's missing is that Dafny needs a "witness" to the
    // there-exists. We need to show an expression that satisfies the
    // body of the exists. Try uncommenting these lines:
    /*{*////*}*/    var o3 := Sandwich(Ham, o1.cheese);
    /*{*////*}*/    assert o3.Sandwich? && o1.cheese == o3.cheese;
    // Simply *mentioning* an Order that satisfies the predicate
    // on o2 above is enough for Dafny to see the proof; once we mention
    // it, Dafny will try plugging it into the expression. Try removing
    // the assertion above this comment; notice that the proof still goes
    // through.
  }
}
