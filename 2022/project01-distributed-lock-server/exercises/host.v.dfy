//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"
//#extract network.t.template solution network.t.dfy

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
/*{*/
  Message() // Populate this datatype.
/*}*/

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    predicate Configure(numHosts: nat, id:HostId) {
      && this.numHosts == numHosts
      && this.myId == id
    }
  }

  datatype Variables = Variables(
/*{*/
    // Fill me in.
/*}*/
  )

  predicate Init(c:Constants, v:Variables) {
/*{*/
  true // Replace me
/*}*/
  }

/*{*/
/*}*/
  // JayNF
  datatype Step =
/*{*/
    | SomeStep   // Replace me
/*}*/

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
/*{*/
  case SomeStep => true
/*}*/
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
