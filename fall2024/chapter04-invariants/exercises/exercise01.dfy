//#title Crawler
//#desc Introduction to inductive invariants
//#desc -- implement the visualization from the lecture.

module Crawler {
  //datatype Constants = Constants()
  datatype Variables = Variables(x:int, y:int)

  ghost predicate Init(v:Variables) {
    && v.x == 0
    && v.y == 5
  }

  ghost predicate MoveNorth(v:Variables, v':Variables) {
    && v'.x == v.x
    && v'.y == v.y + 1
  }

  ghost predicate MoveSouthEast(v:Variables, v':Variables) {
    && v'.x == v.x + 1
    && v'.y == v.y - 1
  }

  ghost predicate Next(v:Variables, v':Variables) {
    || MoveNorth(v, v')
    || MoveSouthEast(v, v')
  }

  ghost predicate InHole(v:Variables) {
    v.x*v.x + v.y*v.y <= 3*3
  }

  ghost predicate Safety(v:Variables) {
    !InHole(v)
  }

  ghost predicate Inv(v:Variables) {
/*{*/
    true  // probably not strong enough. :v)
/*}*/
  }

  // Here's your proof obligation that Safety predicate holds in every behavior
  // allowed by the state machine.
  // With the correct invariant, this proof goes through without a body.
  lemma SafetyTheorem(v:Variables, v':Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
  }
}
