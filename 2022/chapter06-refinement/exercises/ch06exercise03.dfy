//#title Refinement proof for 2PC
//#desc Show that Two Phase Commit refines the Atomic Commit sate machine spec.

// This proof shouldn't be terribly brutal, since you have a roadmap for the
// relevant invariants from chapter05. You can discard the AC properties (since
// those are proven about the spec in exercise03, and therefore about any state
// machine that refines the spec).

include "ch06exercise01.dfy"
//#extract ch06exercise01.template solution ch06exercise01.dfy

// We have provided you with a copy of our solution to chapter05 exercises
// here. We're building on its state machine, so of course we need that
// The thing that chapter 05 considered a "spec" is no longer a spec since
// we're going to use an abstract spec that the protocol refines; however,
// it's still really useful as an invariant, so we'll incorporate that
// property and its proof here as well.
// You could use your own solution to chapter05 in place of this one, if you
// prefer.
include "exercise03.dfy"
//#extract ../../chapter05-distributed-state-machines/exercises/exercise01.template solution exercise01.dfy
//#extract ../../chapter05-distributed-state-machines/exercises/exercise02.template solution exercise02.dfy
//#extract ../../chapter05-distributed-state-machines/exercises/exercise03.template solution exercise03.dfy

// This Dafny "abstract module" establishes the proof obligations for the
// refinement: later in the file you will be obligated to fill in the function
// and lemma bodies in a module that `refines` this one.
// (This structure is a nice way to separate the statement of the theorem from
// its proof.)
abstract module RefinementTheorem {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened TwoPCInvariantProof
  import AtomicCommit

  ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
    requires c.WF()

  ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
    requires v.WF(c)

  ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires DistributedSystem.Init(c, v)
    ensures Inv(c, v)
    ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    requires DistributedSystem.Next(c, v, v', event)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && event == NoOpEvent)

}

module RefinementProof refines RefinementTheorem {
  // No imports needed because we inherited them from the abstract module RefinementTheorem
  import opened Obligations
  import opened CoordinatorHost

  // Here are some handy accessor functions for dereferencing the coordinator
  // and the participants out of the sequence in Hosts.
  ghost function CoordinatorConstants(c: DistributedSystem.Constants) : CoordinatorHost.Constants
    requires c.WF()
  {
    Last(c.hosts).coordinator
  }

  ghost function CoordinatorVars(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : CoordinatorHost.Variables
    requires v.WF(c)
  {
    Last(v.hosts).coordinator
  }

  // Here's a handy function to save you some typing.
  ghost function ParticipantCount(c: DistributedSystem.Constants) : nat
    requires c.WF()
  {
/*{*/
    CoordinatorConstants(c).participantCount // this may change, depending on your implementation
/*}*/
  }

  // The main challenge of setting up a refinement: abstracting from the
  // low-level (protocol) state to the high-level (spec) state.
  ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
  {
/*{*/
    AtomicCommit.Constants(0, [])   // Replace me
/*}*/
  }

  ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
/*{*/
    AtomicCommit.Variables(None, [])   // Replace me
/*}*/
  }

  ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
  {
    // Just point at the invariant from the chapter05 proof (in exercise03).
    // Be certain to fully-qualify the invariant name (mention its module
    // explicily) to avoid inadvertently referring to the shadowing definition
    // RefinementTheorem.Inv.
/*{*/
    false  // Replace me
/*}*/
  }

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    // Obligations inherited from RefinementTheorem.RefinementInit
    // requires DistributedSystem.Init(c, v)
    // ensures Inv(c, v)
    // ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
  {
  }

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    // Obligations inherited from RefinementTheorem.RefinementNext
    // requires DistributedSystem.Next(c, v, v', event)
    // requires Inv(c, v)
    // ensures Inv(c, v')
    // ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && event == NoOpEvent)
  {
    // Advice: appeal to the existing proof to get Inv(c, v')!
/*{*/
/*}*/

    // The "new" part of this proof is to explain which AtomicCommit
    // (spec-level) action happened in response to each 2PC (protocol-level)
    // action. So the general strategy is: use skolemization (var :|) to "learn"
    // which thing happened in the DistributedSystem, split the cases, and
    // assert the right AtomicCommit.NextStep() predicate. Mostly, Dafny needs
    // those asserts because they're witnesses to the `exists` in AtomicCommit.Next().
/*{*/
/*}*/
  }
}
