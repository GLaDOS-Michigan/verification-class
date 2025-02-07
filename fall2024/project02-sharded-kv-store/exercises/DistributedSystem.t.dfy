include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy
include "Host.v.dfy"
//#extract Host.v.template inherit Host.v.dfy

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  type HostId = Network.HostId

/*{*/
  datatype Constants = Constants()
  {
    ghost predicate WF() {
      && true
    }
  }
  datatype Variables = Variables()
  {
    ghost predicate WF(c: Constants) {
      && true
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && true   // define me
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    && true   // define me
  }
/*}*/
}
