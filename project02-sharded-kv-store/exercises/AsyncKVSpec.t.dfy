include "AtomicKV.t.dfy"
//#extract AtomicKV.t.template inherit AtomicKV.t.dfy
include "EventSequenceRecorder.t.dfy"
//#extract EventSequenceRecorder.t.template inherit EventSequenceRecorder.t.dfy


// Identical to chapter08 AsyncWarehouseSpec, except that we're
// asynchronizing AtomicKV instead of AtomicWarehouse.
module AsyncKVSpec {
  import opened Types
  import AtomicKV
  import EventSequenceRecorder

/*{*/
  // Model this after the AsyncWarehouseSpec in chapter08.
  datatype Constants = Constants()  // define me
  datatype Variables = Variables()  // define me

  predicate Init(c: Constants, v: Variables) {
    && true  // define me
  }

  predicate Next(c: Constants, v: Variables, v': Variables, event: Event) {
    && true  // define me
  }
/*}*/
}
