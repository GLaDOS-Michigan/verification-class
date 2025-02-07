//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"
//#extract exercise02.template solution exercise02.dfy

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

/*{*/
/*}*/
  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    true // Replace me
/*}*/
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
/*{*/
/*}*/
    // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(c, v)
    // ...but you'll need more.
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
/*{*/
/*}*/
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
/*{*/
/*}*/
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
