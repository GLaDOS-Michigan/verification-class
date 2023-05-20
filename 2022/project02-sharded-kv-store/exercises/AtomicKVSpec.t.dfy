include "IMapHelpers.t.dfy"
include "Types.t.dfy"

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
// TODO correct: In DistributedSystem you'll use the EventSequenceRecorder to extend this
// atomic definition to an asynchronous one where requests arrive some time
// before execution, and responses are delivered some time after execution.

// TODO correct docs: Identical to chapter08 AsyncWarehouseSpec, except that we're
// asynchronizing AtomicKV instead of AtomicWarehouse.
module AtomicKVSpec {
  import opened IMapHelpers
  import opened Types

  // Model this after the AsyncWarehouseSpec in chapter08.
  datatype Constants = Constants()  // don't need any here
  datatype Variables = Variables(
  /*{*/
    // define me
  /*}*/
  )

  // The initial map should assign the value zero to every key.
  // Be sure to check out IMapHelpers.t.dfy. It's helpful.
  ghost predicate Init(c: Constants, v: Variables) {
  /*{*/
    && true  // define me
  /*}*/
  }

  // TODO replace docs: Model the state machine transition on the AtomicWarehouse module in chapter08.
  /*{*/
  /*}*/

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event) {
    // All the nondeterminism is encoded in `event`! No `exists` required.
    NextStep(c, v, v', event)
  }
}
