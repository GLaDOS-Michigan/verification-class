//#title State Machine Spec for Atomic Commit
//#desc Build an abstract behavioral model that captures the
//#desc semantics of an evolving system to use as a refinement
//#desc reference for its more-complicated implementation.

// Define the specification of atomic commit in the form of a state
// machine.
//
// The abstract model doesn't worry about network communication. Instead,
// it models the input:
//     - which participants prefer which outcomes
// and the outputs:
//     - what the coordinator thinks the decision was
//     - what each participant thinks the decision was
// This definition should make it obvious by inspection that the output decisions
// all agree (AC1) and they output decisions comply with the input preferences
// (AC3, AC4).
//
// In a future exercise, we'll show refinement: that the 2PC protocol correctly
// computes a decision based on all participants' preferences.
//
// Note that this is an assumed-correct spec. This file already passes Dafny,
// but it's a terrible spec, because it doesn't say anything useful. Consider
// running your result past an instructor in office hours to be sure it's a good
// spec.

include "UtilitiesLibrary.dfy"
include "CommitTypes.dfy"

// This is the specification state machine. It defines what the implementation
// is trying to accomplish, while ignoring all implementation details.
module AtomicCommit {
  import opened CommitTypes
  import opened UtilitiesLibrary

  type ParticipantId = nat

  // We'll give you the state data structure; it'll be your job to define the
  // actions.  The input preferences are constant, so we record them here.
  datatype Constants = Constants(participantCount: nat, preferences:seq<Vote>)
  {
    ghost predicate WF() {
      && |preferences| == participantCount
    }
    ghost predicate ValidParticipant(idx: ParticipantId) { idx < participantCount }
  }

  // The outputs are the decision reached by the coordinator and those
  // observed by the participants.
  // None? capture the idea that initially nobody knows the decision.
  // In your actions, make AC2 abundantly obvious: once a None? turns into a
  // Some?, it can't ever change.
  datatype Variables = Variables(coordinatorDecision: Option<Decision>,
                                 participantDecisions: seq<Option<Decision>>)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && |participantDecisions| == c.participantCount
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
/*{*/
    true // Replace me
/*}*/
  }

  // We can tell what the ultimate decision has to be just from the constants.
  // Define that in this function, and then use it to constrain what actions
  // can happen in the state machine.
  ghost function UltimateDecision(c: Constants) : Decision
    requires c.WF()
  {
/*{*/
    Commit // Replace me
/*}*/
  }

/*{*/
/*}*/

  // JayNF
  datatype Step =
/*{*/
    ReplaceMeWithYourJayNFSteps()
/*}*/

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, event: Event, step: Step)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && (
      match step
/*{*/
    case ReplaceMeWithYourJayNFSteps => true
/*}*/
      )
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    exists step :: NextStep(c, v, v', event, step)
  }

  ghost predicate ExecutionSatisfiesSpec(c: Constants, ex: seq<Variables>, evs: seq<Event>)
  {
    && 0 < |ex|
    && |evs| == |ex| - 1
    && (forall i | 0 < i < |ex| :: ex[i].WF(c))
    && Init(c, ex[0])
    && (forall i | 0 <= i < |ex|-1 :: Next(c, ex[i], ex[i+1], evs[i]))
  }

  // Show us an execution that satisfies your state machine and arrives at Commit.
  lemma PseudoLivenessCommit(c: Constants) returns (ex: seq<Variables>, evs: seq<Event>)
    requires c == Constants(2, [Yes, Yes])
    ensures UltimateDecision(c) == Commit
    ensures ExecutionSatisfiesSpec(c, ex, evs)
    // At the end, everybody learns Commit.
    ensures Last(ex).coordinatorDecision == Some(Commit)
    ensures Last(ex).participantDecisions[0] == Some(Commit)
    ensures Last(ex).participantDecisions[1] == Some(Commit)
  {
/*{*/
    ex := [];  // Your execution here.
    evs := []; // Your events here.
/*}*/
  }

  // Show us another execution that satisfies your state machine and arrives at Abort.
  lemma PseudoLivenessAbort(c: Constants) returns (ex: seq<Variables>, evs: seq<Event>)
    requires c == Constants(2, [Yes, No])
    ensures UltimateDecision(c) == Abort
    ensures ExecutionSatisfiesSpec(c, ex, evs)
    // At the end, everybody learns Abort.
    ensures Last(ex).coordinatorDecision == Some(Abort)
    ensures Last(ex).participantDecisions[0] == Some(Abort)
    ensures Last(ex).participantDecisions[1] == Some(Abort)
  {
/*{*/
    ex := [];  // Your execution here.
    evs := []; // Your events here.
/*}*/
  }
}




