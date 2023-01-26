include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy

// The application spec for this system is a key-value store
// that maintains a map of int keys to int values.
// The type of the state in this state machine is simply a total imap: one in
// which every possible key is in the domain.
// The user-visible actions are Get and Put operations.
// Get accepts a key and returns a value.
// Put accepts a key and a value and returns nothing (acknowledging completion).
//
// As in chapter08, we define the spec behavior as an atomic state machine --
// one that consumes an input and delivers an output in a single transition.
// In DistributedSystem you'll use the EventSequenceRecorder to extend this
// atomic definition to an asynchronous one where requests arrive some time
// before execution, and responses are delivered some time after execution.

module AtomicKV {
  import opened IMapHelpers
  import opened Types

  datatype Constants = Constants()

  datatype Variables = Variables(table: imap<int, int>)

  // The initial map should assign the value zero to every key.
  predicate Init(c: Constants, v: Variables) {
/*{*/
    true  // define me
/*}*/
  }

  // Model the state machine transition on the AtomicWarehouse module in chapter08.
/*{*/
/*}*/

  predicate Next(c: Constants, v: Variables, v': Variables, internalOp: InternalOp) {
/*{*/
    true  // define me
/*}*/
  }
}
