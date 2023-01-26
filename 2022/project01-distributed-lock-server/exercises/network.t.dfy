//#title Network
//#desc This file isn't editable because it's a trusted file that specifies how
//#desc the network delivers packets, allowing reorder and duplicate delivery.

include "UtilitiesLibrary.dfy"

module HostIdentifiers {
  type HostId = int // Pretty type synonym (a la C typedef)

  predicate ValidHostId(numHosts: nat, hostid: HostId) {
    0 <= hostid < numHosts
  }

  // The set of all host identities.
  function AllHosts(numHosts: nat) : set<HostId> {
    set hostid:HostId |
      && 0 <= hostid < numHosts // This line is entirely redundant, but it satisfies Dafny's finite-set heuristic; see chapter01 exercise15
      && ValidHostId(numHosts, hostid)
  }
}

// This version of Network uses a template parameter to avoid having to declare
// the Message type before the Network module. (Contrast with ch05/ex02.)
module Network {
  import opened UtilitiesLibrary

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps<Message> = MessageOps(recv:Option<Message>, send:Option<Message>)

  datatype Constants = Constants(numHosts: nat)
  {
    predicate Configure(numHosts: nat) {
      this.numHosts == numHosts
    }
  }

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables<Message> = Variables(sentMsgs:set<Message>)

  predicate Init<Message>(c: Constants, v: Variables<Message>)
  {
    && v.sentMsgs == {}
  }

  predicate Next<Message>(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}
