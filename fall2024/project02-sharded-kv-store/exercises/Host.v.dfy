include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy
include "MessageType.v.dfy"
//#extract MessageType.v.template inherit MessageType.v.dfy
include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy

//
// Your protocol should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKVSpec, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//
// Initially host 0 should own all the keys.
//
// Don't forget about the helper functions in IMapHelpers.t.dfy. They can be
// quite useful!

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

/*{*/
  // Replace these definitions with more meaningful ones that capture the operations
  // of a key-value store described above.
  datatype Constants = Constants()
  datatype Variables = Variables()
/*}*/
}
