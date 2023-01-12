include "AsyncKVSpec.t.dfy"
//#extract AsyncKVSpec.t.template inherit AsyncKVSpec.t.dfy
include "DistributedSystem.t.dfy"
//#extract DistributedSystem.t.template inherit DistributedSystem.t.dfy

abstract module RefinementObligation {
  import opened UtilitiesLibrary
  import opened Types
  import opened DistributedSystem
  import AsyncKVSpec

  function ConstantsAbstraction(c: Constants) : AsyncKVSpec.Constants
    requires c.WF()

  function VariablesAbstraction(c: Constants, v: Variables) : AsyncKVSpec.Variables
    requires v.WF(c)

  predicate Inv(c: Constants, v: Variables)

  lemma RefinementInit(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
    ensures AsyncKVSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  // The key idea in this refinement obligation is that every step of the DistributedSystem
  // has an event label, and that event label must match whatever step of the spec
  // is implied by Player 2's abstraction function.
  lemma RefinementNext(c: Constants, v: Variables, v': Variables, event: Event)
    requires Next(c, v, v', event)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AsyncKVSpec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event)
}
