//#title DistributedSystem
//#desc This file isn't editable because it's a trusted file that specifies how
//#desc hosts interact with one another over the network.

include "host.v.dfy"
//#extract host.v.template solution host.v.dfy

// Before we get here, caller must define a type Message that we'll
// use to instantiate network.s.dfy.

module DistributedSystem {
  import opened HostIdentifiers
  import Host
  import Network

  datatype Constants = Constants(
    hosts:seq<Host.Constants>,
    network:Network.Constants) {
    ghost predicate WF() {
      // Network numHosts and each host's numHosts agree with the size of our
      // own host list
      && network.Configure(|hosts|)
      && (forall id | ValidHostId(id) :: hosts[id].Configure(|hosts|, id))  // every host knows its id (and ids are unique)
    }

    ghost predicate ValidHostId(hostid: HostId) {
      HostIdentifiers.ValidHostId(|hosts|, hostid)
    }
  }

  datatype Variables = Variables(
    hosts:seq<Host.Variables>,
    network:Network.Variables<Host.Message>) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
    }
  }

  ghost predicate Init(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall id | c.ValidHostId(id) :: Host.Init(c.hosts[id], v.hosts[id]))
    && Network.Init(c.network, v.network)
  }

  // JayNF
  datatype Step = Step(id:HostId, msgOps: Network.MessageOps<Host.Message>)

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(step.id)
    && Host.Next(c.hosts[step.id], v.hosts[step.id], v'.hosts[step.id], step.msgOps)
    && (forall other | c.ValidHostId(other) && other != step.id :: v'.hosts[other] == v.hosts[other])
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables) {
    exists step :: NextStep(c, v, v', step)
  }
}
