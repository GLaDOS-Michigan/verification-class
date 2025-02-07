//#title Single-Server Lock Service Proof
//#desc A more realistic invariant proof of the previous chapter's lock
//#desc service.

// Copy your solution for chapter03/exercise03 into the current directory with
// this name:
include "chapter03-exercise03.dfy"
//#extract ../../chapter03-state-machines/exercises/exercise03.template solution chapter03-exercise03.dfy


/*{*/
/*}*/
ghost predicate Inv(c:Constants, v:Variables) {
/*{*/
  true  // Replace me: probably not strong enough. :v)
/*}*/
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(c:Constants, v:Variables, v':Variables)
  ensures Init(c, v) ==> Inv(c, v)
  ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
  ensures Inv(c, v) ==> Safety(c, v)
{
/*{*/
/*}*/
}
