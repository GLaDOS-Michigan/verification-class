
module CommitTypes {
  // How a particular participant feels.
  datatype Vote = Yes | No

  // What decision has been reached by the protocol.
  datatype Decision = Commit | Abort

  // Define events for this state machine (and the ch6 spec state machine it
  // refines).
  datatype Event = ParticipantLearnsEvent(idx: nat) | CoordinatorLearnsEvent() | NoOpEvent()
}
