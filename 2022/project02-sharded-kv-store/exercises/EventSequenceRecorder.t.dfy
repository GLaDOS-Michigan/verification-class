include "UtilitiesLibrary.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy

module EventSequenceRecorder {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants()  // No constants
  datatype Variables = Variables(requests:set<Input>, replies:set<Output>)

  predicate Init(c: Constants, v: Variables)
  {
    // Initialize Variables correctly. Hint: see chapter08
/*{*/
    && true
/*}*/
  }

  // Allow the Host to consume a request and produce a reply.
  //
  // internalOp is a binding variable: protocol says what it'd do if it got that
  // request, and this module gets to say whether a request is available right
  // now, or record the fact that the protocol returned a given result.
  //
  // The Host protocol can consume any request it wants, and introduce any reply
  // it wants; that won't affect meaning, since it ultimately has to get the
  // incoming requests and outgoing replies to match what the spec allows.
  predicate Execute(c: Constants, v: Variables, v': Variables, internalOp: InternalOp)
/*{*/
    requires true  // Fix me. Hint: see chapter08
/*}*/
  {
    // Record that a request has been transformed into a reply.
    // Same idea as in the previous chapter.
/*{*/
    && true  // Define me. Hint: see chapter08
/*}*/
  }

  predicate Internal(c: Constants, v: Variables, v': Variables)
  {
    && v' == v
  }

  // Record the claim that a client actually made this request.
  // This corresponds to a trusted handler attesting that the client wanted the
  // request, it wasn't just invented by the protocol.
  predicate AcceptRequest(c: Constants, v: Variables, v': Variables, request: Input)
  {
    // Record that a client has introduced a new request into the system.
    // Same idea as in the previous chapter.
/*{*/
    && true  // Define me. Hint: see chapter08
/*}*/
  }

  // Ensure there's a reply to deliver to a client, and record the fact that
  // it's been delivered so we can't deliver a duplicate later.
  // This corresponds to a trusted handler attesting that this reply was
  // exposed to the client -- so the spec must justify the exposed value.
  predicate DeliverReply(c: Constants, v: Variables, v': Variables, reply: Output)
  {
    // Record that a reply has been delivered to a client.
    // Same idea as in the previous chapter.
/*{*/
    && true  // Define me. Hint: see chapter08
/*}*/
  }

  predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
/*{*/
    && true  // Define me. Hint: see chapter08
/*}*/
  }
}
