include "UtilitiesLibrary.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy
include "MessageType.v.dfy"
//#extract MessageType.v.template inherit MessageType.v.dfy

module Network {
  import opened UtilitiesLibrary
  import opened Types
  import opened MessageType

  type HostId = nat

  datatype MessageOps = MessageOps(recv: Option<Message>, send: Option<Message>)

  datatype Constants = Constants  // no constants for network

  datatype Variables = Variables(inFlightMessages:set<Message>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.inFlightMessages == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.inFlightMessages)

//////////////////////////////////////////////////////////////////////////////
//     _     ___   ___  _  __  _   _ _____ ____  _____ 
//    | |   / _ \ / _ \| |/ / | | | | ____|  _ \| ____|
//    | |  | | | | | | | ' /  | |_| |  _| | |_) |  _|  
//    | |__| |_| | |_| | . \  |  _  | |___|  _ <| |___ 
//    |_____\___/ \___/|_|\_\ |_| |_|_____|_| \_\_____|
//
// This network model differs from chapter 08. It is a magical network that
// prevents the host from sending a duplicate message until the first copy
// is delivered! A little unrealistic, but it'll make your proof a little
// easier. Read the following comment & conjunct.
//
//////////////////////////////////////////////////////////////////////////////
                                                 
    // Only allow sending a message if there isn't a duplicate of that
    // message already sent but not yet delivered.
    // Two better approaches I didn't take:
    //  * Define the inFlightMessages as a multiset. Turns out this leads
    //    to a much more challenging definition of disjoint in the proof.
    //  * Demand the host provide nonces and do its own duplicate prevention,
    //    proving it as an invariant. Ugh, too much to ask of students.
    // So instead, for this class project, we provide this little helpful
    // leg-up from the trusted network model.
    && (msgOps.send.Some? ==> msgOps.send.value !in v.inFlightMessages)

    // Record the sent message, if there was one.
    && v'.inFlightMessages ==
      v.inFlightMessages
        // remove a message "used up" by receipt
        - (if msgOps.recv.None? then {} else { msgOps.recv.value })
        // add a new message supplied by send
        + (if msgOps.send.None? then {} else { msgOps.send.value })
  }
}
