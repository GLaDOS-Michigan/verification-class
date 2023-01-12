include "EventSequenceRecorder.t.dfy"
//#extract EventSequenceRecorder.t.template inherit EventSequenceRecorder.t.dfy
include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy
include "Host.v.dfy"
//#extract Host.v.template inherit Host.v.dfy

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import EventSequenceRecorder
  import Network
  import Host

  type HostId = Network.HostId

/*{*/
  // Model this module after DistributedSystem in chapter08.
  datatype Constants = Constants()
  {
    predicate WF() {
      && true
    }
  }
  datatype Variables = Variables()
  {
    predicate WF(c: Constants) {
      && true
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && true   // define me
  }

  predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    && true   // define me
  }
/*}*/
}
