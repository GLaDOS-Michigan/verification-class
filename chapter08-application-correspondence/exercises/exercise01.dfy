//#title Sharded Producer Consumer
//#desc How do we prevent a nonsense refinement theorem? For example, suppose the
//#desc protocol-level state machine allows arbitrary behavior, but the refinement
//#desc abstraction function maps every protocol-level state to the initial spec state,
//#desc so it can refine to a bunch of stutter steps?

include "UtilitiesLibrary.dfy"

module Types {
  type Nonce = nat

  datatype Input =
    | ProduceRequest(reqId: Nonce, units: nat)
    | ConsumeRequest(reqId: Nonce, units: nat)
  datatype Output =
    | ProduceReply(request: Input)
    | ConsumeReply(request: Input)
  {
    predicate WF() {
      match this
        case ProduceReply(request) => request.ProduceRequest?
        case ConsumeReply(request) => request.ConsumeRequest?
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
    | AcceptRequestOp(request: Input)
    | DeliverReplyOp(reply: Output)

  // The spec and its protocol will see only the InternalOps, which gets
  // to either handle a single request, or do some background activity.
  // This corresponds to, say, an implementation handler being invoked with a
  // request and having a reply as its return type. The ESR also observes these
  // "handler" events, and the refinement will require the Host to justify all
  // of its actions as being requested by such events.
  datatype InternalOp =
    | ExecuteOp(request: Input, reply: Output)
    | InternalNoop()

  datatype Event =
    | ExternalEvent(clientOp: ClientOp)
    | InternalEvent(internalOp: InternalOp)
}

// The Event Sequence Recorder is a state machine that observes which requests
// have been issued by a client, which have been executed (turned into
// replies), and which replies have been delivered back to the client.
// We're taking the idea of capturing linearizability by recording
// client-observable request begin- and end-times as in the previous chapter,
// and bundling it up into a self-contained state machine. That lets us use this
// abstract notion of request asynchrony to both define the spec, where we need
// it to ensure linearizability is well-defined, and the distributed system,
// where we need to record the requests the protocol is executing to ensure
// that they're really accounted for in the refinement to the spec.

// This state machine is analogous to the network: it's a trusted module that
// gets connected to the host protocol via a binding variable. The host says
// "if the client were to initiate this request, here's how I'd respond;" this
// module gets to say "whether the client initiated this request".  (Just as
// the network says whether a packet can be received.) This represents the
// trusted system "observing" requests crossing between the application and the
// protocol (eg at a library boundary), to ensure that the protocol proof isn't
// succeeding by simply lying about the client requesting things it never did.

module EventSequenceRecorder {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants()  // No constants
  datatype Variables = Variables(requests:set<Input>, replies:set<Output>)

  predicate Init(c: Constants, v: Variables)
  {
    // Initialize Variables correctly. Same idea as in the previous chapter.
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
    requires internalOp.ExecuteOp?
  {
    // Record that a request has been transformed into a reply.
    // Same idea as in the previous chapter.
/*{*/
    && true 
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
    && true
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
    && true
/*}*/
  }

  predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    match event
      case ExternalEvent(clientOp) => (
        match clientOp
          case AcceptRequestOp(request) => AcceptRequest(c, v, v', request)
          case DeliverReplyOp(reply) => DeliverReply(c, v, v', reply)
      )
      case InternalEvent(internalOp) => (
        match internalOp
          case ExecuteOp(_, _) => Execute(c, v, v', internalOp)
          case InternalNoop() => Internal(c, v, v')
      )
  }
}

// An atomic (non-async) model of the warehouse spec: it highlights just the
// "business logic"; we'll glue the async client interactions on later.
module AtomicWarehouse {
  import opened Types

  datatype Constants = Constants()
  datatype Variables = Variables(inventory: nat)

  predicate Produce(c: Constants, v: Variables, v': Variables, internalOp: InternalOp)
    requires internalOp.ExecuteOp?
    requires internalOp.request.ProduceRequest?
  {
    && internalOp.reply == ProduceReply(internalOp.request)
    && v'.inventory == v.inventory + internalOp.request.units
  }

  predicate Consume(c: Constants, v: Variables, v': Variables, internalOp: InternalOp)
    requires internalOp.ExecuteOp?
    requires internalOp.request.ConsumeRequest?
  {
    && internalOp.reply == ConsumeReply(internalOp.request)
    && internalOp.request.units <= v.inventory
    && v'.inventory == v.inventory - internalOp.request.units
  }

  predicate Internal(c: Constants, v: Variables, v': Variables, internalOp: InternalOp)
  {
    && v' == v
  }

  predicate Init(c: Constants, v: Variables) {
    && v.inventory == 0
  }

  predicate Next(c: Constants, v: Variables, v': Variables, internalOp: InternalOp) {
    match internalOp
      case ExecuteOp(_, _) => (
        match internalOp.request
          case ProduceRequest(_, _) => Produce(c, v, v', internalOp)
          case ConsumeRequest(_, _) => Consume(c, v, v', internalOp)
          )
      case InternalNoop() => Internal(c, v, v', internalOp)
  }
}

// The ultimate application spec ("top bread") is just a compound of the
// AtomicWarehouse business logic with the EventSequenceRecorder async client interface.
module AsyncWarehouseSpec {
  import opened Types
  import AtomicWarehouse
  import EventSequenceRecorder

  datatype Constants = Constants(
    app: AtomicWarehouse.Constants,
    events: EventSequenceRecorder.Constants
  )

  datatype Variables = Variables(
    app: AtomicWarehouse.Variables,
    events: EventSequenceRecorder.Variables
  )

  predicate Init(c: Constants, v: Variables) {
    && AtomicWarehouse.Init(c.app, v.app)
    && EventSequenceRecorder.Init(c.events, v.events)
  }

  // Transitions of this trusted spec are *labeled* with an event so we can
  // require the refinement to preserve events observed at the trusted physical
  // ESR boundary in the implementation.
  predicate Next(c: Constants, v: Variables, v': Variables, event: Event) {
    // EventSequenceRecorder observes every event
    && EventSequenceRecorder.Next(c.events, v.events, v'.events, event)
    // App "business logic" observes only InternalEvents.
    && match event
        case ExternalEvent(clientOp)
          => v'.app == v.app
        case InternalEvent(internalOp)
          => AtomicWarehouse.Next(c.app, v.app, v'.app, internalOp)
  }
}

//////////////////////////////////////////////////////////////////////////////
// From here down we're building up the distributed system that implements
// the spec given above.
//////////////////////////////////////////////////////////////////////////////

// In this exercise, unlike Chapter 5, the network promises to deliver
// messages at most once. Having that assumption available makes the
// Host less complicated to describe. Think of it as assuming that
// TCP (or some other duplicate-elimination mechanism) is part of the system's
// trusted computing base, below the "bottom bread".
//
// This module isn't part of Types because Types is trusted but this module
// needn't be.
module MessageType {
  // A network message indicating that `count` items have been removed from the
  // sender's warehouse to be stored in the receiver's warehouse.
  datatype Message = TransferMsg(units: nat)
}

// Read this Network carefully. Unlike prior exercises, here we use a Network
// that delivers each message at most once.
module Network {
  import opened UtilitiesLibrary
  import opened Types
  import opened MessageType

  type HostId = nat

  datatype MessageOps = MessageOps(recv: Option<Message>, send: Option<Message>)

  datatype Constants = Constants  // no constants for network

  // Network state is the multiset of messages in flight. Delivering a message
  // removes it from the multiset. It's a multiset because, if the same message
  // is sent twice, we can't disappear one of them.
  datatype Variables = Variables(inFlightMessages:multiset<Message>)

  predicate Init(c: Constants, v: Variables)
  {
    && v.inFlightMessages == multiset{}
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.inFlightMessages)
    // Record the sent message, if there was one.
    && v'.inFlightMessages ==
      v.inFlightMessages
        // remove a message "used up" by receipt
        - (if msgOps.recv.None? then multiset{} else multiset{ msgOps.recv.value })
        // add a new message supplied by send
        + (if msgOps.send.None? then multiset{} else multiset{ msgOps.send.value })
  }
}

// This is the "untrusted" (verified) protocol description that Player 2 wrote.
// It describes how a single host behaves to implement its part of the distributed
// system.
module Host {
  import opened UtilitiesLibrary
  import opened Types
  import opened MessageType
  import EventSequenceRecorder
  import Network

  type HostId = Network.HostId

  datatype Constants = Constants(myId: HostId) {
    predicate GroupWF(id: HostId) {
      && myId == id
    }
  }

  datatype Variables = Variables(
    inventory: nat  // This is the local inventory at this Host's "warehouse"
  )

  predicate Init(c: Constants, v: Variables)
  {
    && v.inventory == 0
  }

  predicate Produce(c: Constants, v: Variables, v': Variables, internalOp: InternalOp, msgOps: Network.MessageOps)
    // This precondition is already checked in NextStep's case
    requires internalOp.ExecuteOp?
    requires internalOp.request.ProduceRequest?
  {
    && var request := internalOp.request;
    && internalOp.reply == ProduceReply(request)
    && msgOps == Network.MessageOps(None, None)
    && v' == v.(inventory := v.inventory + request.units)
  }

  predicate Consume(c: Constants, v: Variables, v': Variables, internalOp: InternalOp, msgOps: Network.MessageOps)
    // This precondition is already checked in NextStep's case
    requires internalOp.ExecuteOp?
    requires internalOp.request.ConsumeRequest?
  {
    && var request := internalOp.request;
    && internalOp.reply == ConsumeReply(request)
    && msgOps == Network.MessageOps(None, None)
    && request.units <= v.inventory   // Must have sufficient inventory locally
    && v' == v.(inventory := v.inventory - request.units)
  }
  
  predicate SendTransfer(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && var transferMsg := msgOps.send.value;
    && transferMsg.TransferMsg?
    && 0 < transferMsg.units <= v.inventory
    && v' == v.(inventory := v.inventory - transferMsg.units)
  }

  predicate ReceiveTransfer(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && var transferMsg := msgOps.recv.value;
    && transferMsg.TransferMsg?
    && v' == v.(inventory := v.inventory + transferMsg.units)
  }

  datatype Step =
    | ExecuteOpStep()       // Process a client request: that is, produce or consume; internalOp tells us what to do
    | SendTransferStep()    // internal step (looks like noop to spec)
    | ReceiveTransferStep() // internal step (looks like noop to spec)

  predicate NextStep(c: Constants, v: Variables, v': Variables, internalOp: InternalOp, msgOps: Network.MessageOps, step: Step)
  {
    match step
      case ExecuteOpStep => (
        && internalOp.ExecuteOp?
        && match internalOp.request
          case ProduceRequest(_, _) => Produce(c, v, v', internalOp, msgOps)
          case ConsumeRequest(_, _) => Consume(c, v, v', internalOp, msgOps)
      )
      case SendTransferStep =>
        && internalOp.InternalNoop?
        && SendTransfer(c, v, v', msgOps)
      case ReceiveTransferStep =>
        && internalOp.InternalNoop?
        && ReceiveTransfer(c, v, v', msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables, internalOp: InternalOp, msgOps: Network.MessageOps)
  {
    exists step: Step :: NextStep(c, v, v', internalOp, msgOps, step)
  }
}


// This is the trusted distributed system compound state machine that ties
// copies of the untrusted Host protocol together with an instance of the
// EventSequenceRecorder state machine. Observe what kinds of interactions it allows -- in
// particular, convince yourself that Player 2 can't synthesize a client Request
// from whole cloth; the EventSequenceRecorder has to do that.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import EventSequenceRecorder
  import Network
  import Host

  type HostId = Network.HostId

  datatype Constants = Constants(hosts: seq<Host.Constants>, events: EventSequenceRecorder.Constants, network: Network.Constants)
  {
    predicate ValidHost(idx: HostId) {
      idx < |hosts|
    }
    predicate WF() {
      && 0 < |hosts|
      // configure each host with its id
      && (forall idx: HostId | ValidHost(idx) :: hosts[idx].GroupWF(idx))
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    events: EventSequenceRecorder.Variables,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall idx: HostId | c.ValidHost(idx) :: Host.Init(c.hosts[idx], v.hosts[idx]))
    && EventSequenceRecorder.Init(c.events, v.events)
    && Network.Init(c.network, v.network)
  }

  // Have ESR module record an incoming request or delivers a reply;
  // no host does anything.
  predicate ClientOpAction(c: Constants, v: Variables, v': Variables, event: Event)
  {
    && v.WF(c)
    && v'.WF(c)
/*{*/
    // Define this predicate. You're defining trusted bottom-bread spec now, so be careful!
    && true
    
/*}*/
  }

  // I named this subpredicate because I use it repeatedly in the proof
  predicate OneHostChanged(c: Constants, v: Variables, v': Variables, hostId: HostId)
    requires v.WF(c) && v'.WF(c)
    requires c.ValidHost(hostId)
  {
    // All other hosts idle.
    && (forall otherIdx: HostId | c.ValidHost(otherIdx) && otherIdx != hostId :: v'.hosts[otherIdx] == v.hosts[otherIdx])
  }

  predicate HostOpAction(c: Constants, v: Variables, v': Variables, event: Event, msgOps: Network.MessageOps, hostId: HostId)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(hostId)

    // This action only applies to internal events (that Player 2's Host protocol can see)
    && event.InternalEvent?

    // Record that this execute event consumed a request and created a reply.
    && EventSequenceRecorder.Next(c.events, v.events, v'.events, event)

    // Network interacts with host's recv/send
    && Network.Next(c.network, v.network, v'.network, msgOps)

    // One host takes a step, interacting with ESR & network as allowed above
    && Host.Next(c.hosts[hostId], v.hosts[hostId], v'.hosts[hostId], event.internalOp, msgOps)
    // All other hosts idle.
    && OneHostChanged(c, v, v', hostId)
  }

  datatype Step =
    | ClientStep()
    | HostStep(msgOps: Network.MessageOps, hostId: HostId)

  predicate NextStep(c: Constants, v: Variables, v': Variables, event: Event, step: Step)
  {
    && match step
        case ClientStep() => ClientOpAction(c, v, v', event)
        case HostStep(msgOps, hostId) => HostOpAction(c, v, v', event, msgOps, hostId)
  }

  predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    exists step :: NextStep(c, v, v', event, step)
  }
}

// This is the "theorem statement": the inductive obligation that there exists
// an abstraction function from distributed system state to the spec state such
// that every execution of the distributed system gives rise to a corresponding
// refined execution that satisfies the spec state machine.
abstract module RefinementObligation {
  import opened UtilitiesLibrary
  import opened Types
  import opened DistributedSystem
  import AsyncWarehouseSpec

  function ConstantsAbstraction(c: Constants) : AsyncWarehouseSpec.Constants
    requires c.WF()

  function VariablesAbstraction(c: Constants, v: Variables) : AsyncWarehouseSpec.Variables
    requires v.WF(c)

  predicate Inv(c: Constants, v: Variables)

  lemma RefinementInit(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
    ensures AsyncWarehouseSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  // The key idea in this refinement obligation is that every step of the DistributedSystem
  // has an event label, and that event label must match whatever step of the spec
  // is implied by Player 2's abstraction function.
  lemma RefinementNext(c: Constants, v: Variables, v': Variables, event: Event)
    requires Next(c, v, v', event)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AsyncWarehouseSpec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event)
}

// We have provided the refinement proof, but you'll have to fill in the Abstraction
// function for the proof to go through. 
module RefinementProof refines RefinementObligation {
  import opened MessageType
  import AtomicWarehouse
  
  function ConstantsAbstraction(c: Constants) : AsyncWarehouseSpec.Constants
// precondition assumed by RefinementObligation:
//    requires c.WF()
  {
    AsyncWarehouseSpec.Constants(AtomicWarehouse.Constants(), EventSequenceRecorder.Constants())
  }

  function SumOfHostInventoryInner(c: Constants, v: Variables, count: nat) : nat
    requires v.WF(c)
    requires count <= |c.hosts|
  {
    if count==0
    then 0
    else SumOfHostInventoryInner(c, v, count-1) + v.hosts[count-1].inventory
  }

  function SumOfHostInventory(c: Constants, v: Variables) : nat
    requires v.WF(c)
  {
    SumOfHostInventoryInner(c, v, |c.hosts|)
  }

  function StableChooseMsg(msgs: multiset<Message>) : Message
    requires 0 < |msgs|
  {
      var msg :| msg in msgs; msg
  }

  function SumOfNetworkInventoryInner(msgs: multiset<Message>) : nat
  {
    if |msgs| == 0
    then 0
    else
      var msg := StableChooseMsg(msgs);
      SumOfNetworkInventoryInner(msgs - multiset{msg}) + msg.units
  }

  function SumOfNetworkInventory(c: Constants, v: Variables) : nat
  {
    SumOfNetworkInventoryInner(v.network.inFlightMessages)
  }

  function VariablesAbstraction(c: Constants, v: Variables) : AsyncWarehouseSpec.Variables
// precondition assumed by RefinementObligation:
//    requires v.WF(c)
  {
/*{*/
    // This is a dummy expression that typechecks. Replace it with the appropriate
    // abstraction function.
    var nonsense: AsyncWarehouseSpec.Variables :| true;
    nonsense
/*}*/
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)

    // We told you the goal of correspondence was that the request and reply
    // stream we see at the lower level (DistributedSystem) is the same as
    // the one we see at the spec level (AsyncWarehouseSpec). The stream of Events
    // is that evidence (each event says what requests and replies came and went).
    // To drive that point home, observe that it's easy to prove that the request
    // and replies fields inside each level's state stay in sync.
    && VariablesAbstraction(c, v).events == v.events
  }

  lemma RefinementHonorsApplicationCorrespondence(c: Constants, v: Variables)
    requires v.WF(c)
    requires Inv(c, v)
    ensures VariablesAbstraction(c, v).events.requests == v.events.requests
    ensures VariablesAbstraction(c, v).events.replies == v.events.replies
  {
    // Now this lemma is trivial, from the conjunct in the Inv.
  }

  lemma RefinementInit(c: Constants, v: Variables)
// preconditions assumed by RefinementObligation:
//    requires c.WF()
//    requires Init(c, v)
    ensures AsyncWarehouseSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    ensures Inv(c, v)
  {
    // Bang out a quick inductive proof that the recursive sum of empty host
    // inventories adds up to zero.
    var count := 0;
    while count<|c.hosts|
      invariant count<=|c.hosts|
      invariant SumOfHostInventoryInner(c, v, count) == 0
    {
      count := count + 1;
    }
  }

  // If a subsequence of the host inventories are the same, they add up the same.
  lemma HostInventorySameLemma(c: Constants, v: Variables, v': Variables, count: nat)
    requires v.WF(c) && v'.WF(c)
    requires count <= |c.hosts|
    requires forall idx:HostId | idx < count
      :: v'.hosts[idx].inventory == v.hosts[idx].inventory
    ensures SumOfHostInventoryInner(c, v', count) == SumOfHostInventoryInner(c, v, count)
  {
    if 0 < count {
      HostInventorySameLemma(c, v, v', count-1);
    }
  }

  // HostInventorySum is built up recursively by summing the hosts' values
  // one element at a time, in whatever order those hosts happen to be in.
  // We need to generalize that definition into something -- a forall statement
  // -- that doesn't care about order (since + is commutative), so we can
  // talk about what happens as we modify this or that arbitrary host index.
  lemma HostInventoryChangeLemma(c: Constants, v: Variables, v': Variables, changedIdx: HostId, delta: int, count: nat)
    requires v.WF(c) && v'.WF(c)
    requires forall idx:HostId | c.ValidHost(idx)
      :: v'.hosts[idx].inventory == v.hosts[idx].inventory + if idx==changedIdx then delta else 0
    requires changedIdx < count <= |c.hosts|
    ensures SumOfHostInventoryInner(c, v', count) == SumOfHostInventoryInner(c, v, count) + delta
  {
    if changedIdx == count - 1 {
      HostInventorySameLemma(c, v, v', count - 1);
    } else {
      HostInventoryChangeLemma(c, v, v', changedIdx, delta, count-1);
    }
  }

  // NetworkInventorySum is built up recursively by taking the multiset apart
  // one element at a time, that element chosen arbitrarily by the :| operator.
  // We need to drag the commutativity of + out of that recursive definition
  // so that we have a way to compare two different multisets.
  lemma NetworkInventorySumDistributesLemma(x: multiset<Message>, y: multiset<Message>)
    ensures SumOfNetworkInventoryInner(x+y) == SumOfNetworkInventoryInner(x)+SumOfNetworkInventoryInner(y)
    decreases |x| + |y|, |x|, |y|
  {
    // The general cases find some element in one or the other set, remove it,
    // and recurse. So first let's dispatch with a couple corner cases that
    // interfere with those general cases.
    if |x|==0 && |y|==0 { return; }
    if |x|==0 {
      assert x+y == y;  // trigger
      return;
    }

    var m := StableChooseMsg(x+y);
    var sm := multiset{m};
    if m in x {
      NetworkInventorySumDistributesLemma(x-sm, sm);
      assert x == x - sm + sm;  // trigger
      assert x + y - sm == x - sm + y;  // trigger
      NetworkInventorySumDistributesLemma(x-sm, y);
    } else {  // symmetric case
      NetworkInventorySumDistributesLemma(y-sm, sm);
      assert y == y - sm + sm;  // trigger
      assert x + y - sm == x + (y - sm);  // trigger
      NetworkInventorySumDistributesLemma(x, y-sm);
    }
  }

  lemma NetworkInventoryChangeLemma(small: multiset<Message>, big: multiset<Message>, addMsg: Message)
    requires big == small + multiset{addMsg}
    ensures SumOfNetworkInventoryInner(big) == SumOfNetworkInventoryInner(small) + addMsg.units
  {
    NetworkInventorySumDistributesLemma(small, multiset{addMsg});
  }

  lemma RefinementNext(c: Constants, v: Variables, v': Variables, event: Event)
// preconditions assumed by RefinementObligation:
//    requires Inv(c, v)
//    requires Next(c, v, v', event)
    ensures Inv(c, v')
    ensures AsyncWarehouseSpec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event)
  {
    var step :| NextStep(c, v, v', event, step);
    match step
      case ClientStep() => {
        assert event.ExternalEvent?;
        HostInventorySameLemma(c, v, v', |c.hosts|);
        assert v.network == v'.network; // trigger for SumOfNetworkInventory unchanged
      }
      case HostStep(msgOps, hostId) => {
        var hc := c.hosts[hostId];
        var hv := v.hosts[hostId];
        var hv' := v'.hosts[hostId];
        var hostStep :| Host.NextStep(hc, hv, hv', event.internalOp, msgOps, hostStep);

        match hostStep
          case ExecuteOpStep => {
            assert v'.network == v.network; // trigger for SumOfNetworkInventory unchanged
            match event.internalOp.request
              case ProduceRequest(_, units) => {
                HostInventoryChangeLemma(c, v, v', hostId, units, |c.hosts|);
              }
              case ConsumeRequest(_, units) => {
                HostInventoryChangeLemma(c, v, v', hostId, -(units as int), |c.hosts|);
              }
          }
          case SendTransferStep => {
            HostInventoryChangeLemma(c, v, v', hostId, -(msgOps.send.value.units as int), |c.hosts|);
            NetworkInventoryChangeLemma(v.network.inFlightMessages, v'.network.inFlightMessages, msgOps.send.value);
          }
          case ReceiveTransferStep => {
            HostInventoryChangeLemma(c, v, v', hostId, msgOps.recv.value.units, |c.hosts|);
            // Note swapped v', v to run lemma backwards:
            NetworkInventoryChangeLemma(v'.network.inFlightMessages, v.network.inFlightMessages, msgOps.recv.value);
          }
      }
  }
}


