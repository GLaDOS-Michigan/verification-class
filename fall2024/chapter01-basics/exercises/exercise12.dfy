//#title include directive and Union (sum) datatypes

// You can include code from another file. includes must all appear at the
// beginning of a file, before any other definitions.
// Open and read DirectionsLibrary.dfy
include "DirectionsLibrary.dfy"

lemma TwoWrongsDontMakeARight(dir:Direction)
{
  assert TurnLeft(/*{*/TurnLeft(TurnLeft(dir))/*}*/) == TurnRight(TurnRight(dir));
}
