include "AtomicKVSpec.t.dfy"
//#extract AtomicKVSpec.t.template inherit AtomicKVSpec.t.dfy
include "DistributedSystem.t.dfy"
//#extract DistributedSystem.t.template inherit DistributedSystem.t.dfy

abstract module RefinementObligation {
  import opened UtilitiesLibrary
  import opened Types
  import opened DistributedSystem
  import AtomicKVSpec

  ghost function ConstantsAbstraction(c: Constants) : AtomicKVSpec.Constants
    requires c.WF()

  ghost function VariablesAbstraction(c: Constants, v: Variables) : AtomicKVSpec.Variables
    requires v.WF(c)

  ghost predicate Inv(c: Constants, v: Variables)

  lemma RefinementInit(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
    ensures AtomicKVSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  // The key idea in this refinement obligation is that every step of the DistributedSystem
  // has an event label, and that event label must match whatever step of the spec
  // is implied by Player 2's abstraction function.
  lemma RefinementNext(c: Constants, v: Variables, v': Variables, event: Event)
    requires Next(c, v, v', event)
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicKVSpec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), event)
}
