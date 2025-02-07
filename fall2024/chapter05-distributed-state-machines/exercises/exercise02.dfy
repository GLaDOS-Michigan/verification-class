//#title Two Phase Commit Safety Specification Predicate
//#desc Express the English Atomic Commit safety properties as predicates
//#desc over the compound state machine model from exercise01.

// 2PC should satisfy the Atomic Commit specification. English design doc:
//
// AC-1: All processes that reach a decision reach the same one.
// AC-3: The Commit decision can only be reached if all processes prefer Yes.
// AC-4: If all processes prefer Yes, then the decision must be Commit.
//
// Note that the full Atomic Commit spec includes these additional properties,
// but you should ignore them for this exercise:
// AC-2: (stability) A process cannot reverse its decision after it has reached one.
//       (best modeled with refinement)
// AC-5: (liveness) All processes eventually decide.

// Note that we include the model of exercise01, so you should write your
// spec accordingly. Of course, that also means double-checking that your
// model performs all actions as described.
include "exercise01.dfy"
//#extract exercise01.template solution exercise01.dfy

module Obligations {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

/*{*/
/*}*/

  // AC-1: All processes that reach a decision reach the same one.
  ghost predicate SafetyAC1(c: Constants, v: Variables)
    requires v.WF(c)
  {
    // All hosts that reach a decision reach the same one
/*{*/
    true // Replace me
/*}*/
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  ghost predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    true // Replace me
/*}*/
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    true // Replace me
/*}*/
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }
}
