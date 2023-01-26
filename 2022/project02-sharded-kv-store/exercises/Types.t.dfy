module Types {
  type Nonce = nat

  // Read the AtomicKV spec file to learn what the inputs and outputs
  // to the system should be, and encode them here.

  datatype Input =
/*{*/
    | SomeRequest()  // Replace me
/*}*/
  datatype Output =
/*{*/
    | SomeReply()  // Replace me
/*}*/
  {
    predicate WF() {
/*{*/
      true
/*}*/
    }
  }

  // AcceptRequest is the trusted client submitting the syscall
  //     (or library call or network request),
  // InternalOp is the implementation handling the syscall and filling in the reply,
  // DeliverReply is the client later learning the value of the reply.

  // The Event Sequence Recorder observes clients making requests and receiving
  // replies.  The application (in the spec layer) or the protocol (in the
  // distributed system layer) does not observe these external events except
  // when they show up for execution as InternalOps.
  datatype ClientOp =
/*{*/
    | SomeClientOp()  // Replace me
/*}*/

  // The spec and its protocol will see only the InternalOps, which gets
  // to either handle a single request, or do some background activity.
  // This corresponds to, say, an implementation handler being invoked with a
  // request and having a reply as its return type. The ESR also observes these
  // "handler" events, and the refinement will require the Host to justify all
  // of its actions as being requested by such events.
  datatype InternalOp =
/*{*/
    | SomeInternalOp()  // Replace me
/*}*/

  datatype Event =
/*{*/
    | SomeEvent()  // Replace me
/*}*/
}

