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
  ghost predicate VoteMessagesAgreeWithParticipantPreferences(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.VoteMsg?
      && ValidParticipantId(c, msg.sender)
      :: msg.vote == ParticipantConstants(c, msg.sender).preference
    )
  }

  ghost predicate CoordinatorStateSupportedByVote(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (forall idx:HostId |
      && ValidParticipantId(c, idx)
      && CoordinatorVars(c, v).votes[idx].Some?
      :: VoteMsg(idx, CoordinatorVars(c, v).votes[idx].value) in v.network.sentMsgs
    )
  }

/*}*/
  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.DecisionMsg?
      :: CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v), msg.decision)
    )
/*}*/
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
/*{*/
    && VoteMessagesAgreeWithParticipantPreferences(c, v)
    && CoordinatorStateSupportedByVote(c, v)
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
    // Nobody has agreed with anything yet, so they agree with both.
    assert AllWithDecisionAgreeWithThisOne(c, v, Commit); // witness.
    assert AllWithDecisionAgreeWithThisOne(c, v, Abort); // witness.
/*}*/
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables, event: Event)
    requires Inv(c, v)
    requires Next(c, v, v', event)
    ensures Inv(c, v')
  {
/*{*/
    // The body of this lemma got really big (expanding foralls, case splits,
    // testing asserts) while I was figuring out what invariants were missing
    // ... and fixing a couple of errors in the protocol definition itself.
    // Afterward, nearly all of that text could be deleted.
    // Manos: now with Dafny 3.8.1, all of it can be deleted.
    // Tej: this proof was flaky in Dafny 4.0.0 and 4.1.0. It probably could go
    // through automatically, but it's fairly big and requires a high
    // rlimit/lots of case splitting.
    var step :| NextStep(c, v, v', event, step);
    if v.hosts[step.hostid].CoordinatorVariables? {
      match step {
        case HostActionStep(hostId, msgOps) => {
          assert hostId == |c.hosts| - 1; // this is the coordinator
          forall msg |
            && msg in v'.network.sentMsgs
            && msg.DecisionMsg?
            ensures CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v'), msg.decision) {
            var coordStep :| CoordinatorHost.NextStep(CoordinatorConstants(c), CoordinatorVars(c, v), CoordinatorVars(c, v'), event, coordStep, msgOps);
            match coordStep {
              case LearnVoteStep => {
                assert msgOps.send.None?;
                // vote matches old vote
                assert CoordinatorVars(c, v') == CoordinatorVars(c, v);
                assert CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v'), msg.decision);
              }
              case SendReqStep => {
                assert CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v'), msg.decision);
              }
              case DecideStep(decision) => {
                assert CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v'), msg.decision);
              }
            }
          }
          assert DecisionMsgsAgreeWithDecision(c, v');
          assert VoteMessagesAgreeWithParticipantPreferences(c, v');
          assert CoordinatorStateSupportedByVote(c, v');
        }
      }
    }
/*}*/
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
