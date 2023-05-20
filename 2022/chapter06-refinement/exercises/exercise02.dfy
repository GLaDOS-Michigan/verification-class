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
  // Here are some handy accessor functions for dereferencing the coordinator
  // and the participants out of the sequence in Hosts.
  ghost function CoordinatorConstants(c: Constants) : CoordinatorHost.Constants
    requires c.WF()
  {
    Last(c.hosts).coordinator
  }

  ghost function CoordinatorVars(c: Constants, v: Variables) : CoordinatorHost.Variables
    requires v.WF(c)
  {
    Last(v.hosts).coordinator
  }

  ghost predicate ValidParticipantId(c: Constants, hostid: HostId)
  {
    hostid < |c.hosts|-1
  }

  ghost function ParticipantConstants(c: Constants, hostid: HostId) : ParticipantHost.Constants
    requires c.WF()
    requires ValidParticipantId(c, hostid)
  {
    c.hosts[hostid].participant
  }

  ghost function ParticipantVars(c: Constants, v: Variables, hostid: HostId) : ParticipantHost.Variables
    requires v.WF(c)
    requires ValidParticipantId(c, hostid)
  {
    v.hosts[hostid].participant
  }

  ghost predicate AllWithDecisionAgreeWithThisOne(c: Constants, v: Variables, decision: Decision)
    requires v.WF(c)
  {
    && (CoordinatorVars(c, v).decision.Some? ==> CoordinatorVars(c, v).decision.value == decision)
    && (forall hostid:HostId
      | ValidParticipantId(c, hostid) && ParticipantVars(c, v, hostid).decision.Some?
      :: ParticipantVars(c, v, hostid).decision.value == decision)
  }
/*}*/

  // AC-1: All processes that reach a decision reach the same one.
  ghost predicate SafetyAC1(c: Constants, v: Variables)
    requires v.WF(c)
  {
    // All hosts that reach a decision reach the same one
/*{*/
    // HAND-GRADE
    // All hosts that reach a decision reach the same one
    || AllWithDecisionAgreeWithThisOne(c, v, Commit)
    || AllWithDecisionAgreeWithThisOne(c, v, Abort)
/*}*/
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  ghost predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    // HAND-GRADE
    // Any host with a No preference forces an abort.
    (exists hostid:HostId ::
        && ValidParticipantId(c, hostid)
        && ParticipantConstants(c, hostid).preference.No?)
    ==> AllWithDecisionAgreeWithThisOne(c, v, Abort)
/*}*/
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    // HAND-GRADE
    // If every host has a Yes preference we must commit.
    (forall hostid:HostId | ValidParticipantId(c, hostid) :: ParticipantConstants(c, hostid).preference.Yes?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Commit)
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
