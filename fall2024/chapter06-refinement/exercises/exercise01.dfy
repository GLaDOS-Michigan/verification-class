//#title Event-based refinement
//#desc You are asked to provide the abstraction function and refinement proof
//#desc for a system describing the interactions among baristas and clients
//#desc when handing out, receiving and transfering bathroom keys.

include "UtilitiesLibrary.dfy"

// These are the world-visible events 
module Events {
    datatype Event =
        // A customer acquires a bathroom key (zip-tied to an oversized spoon) from the Starbucks staff
          Acquire
        // Some customer returns a key to the staff.
        | Release
        | NoOp
}

// This is the high-level specification
module Spec {
    import opened Events

    datatype Constants = Constants(
        // The total number of available bathroom keys (one per stall, I guess?)
        totalKeys: nat
    )

    datatype Variables = Variables(
        // The number of keys not presently held by customers.
        availableKeys: nat
    )

    ghost predicate Init(c: Constants, v: Variables) {
        && v.availableKeys == c.totalKeys
    }

    ghost predicate CustomerAcquiresKey(c: Constants, v: Variables, v': Variables) {
        && 0 < v.availableKeys
        && v'.availableKeys == v.availableKeys - 1
    }

    ghost predicate CustomerReleasesKey(c: Constants, v: Variables, v': Variables) {
        // As player 1, we know it's impossible for a customer to return a key
        // beyond the total number that exist.
        && v.availableKeys < c.totalKeys
        && v'.availableKeys == v.availableKeys + 1
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case Acquire => CustomerAcquiresKey(c, v, v')
            case Release => CustomerReleasesKey(c, v, v')
            case NoOp => v' == v
        }
    }

}

//////////////////////////////////////////////////////////////////////////////

module Types {
    import opened UtilitiesLibrary

    type HostId = nat

    // a positive keyDelta means the number of keys added to the basket
    // a negative keyDelta means the number of keys removed from the basket
    datatype BasketOp = BasketOp(keyDelta:int)
}

// The (untrusted) host/barista model.
// This has been implemented for you in this exercise 
module Host {
    import opened Events
    import opened Types
    import opened UtilitiesLibrary

    datatype Constants = Constants()

    datatype Variables = Variables(
        // A host in this exercise is a barista who has some number of bathroom keys
        // in their apron.
        keysInApron: nat
    )

    ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, initialKeys: nat)
    {
        forall idx | 0 <= idx < |grp_v| :: grp_v[idx].keysInApron == if idx == 0 then initialKeys else 0
    }

    ghost predicate CustomerAcquiresKey(c: Constants, v: Variables, v': Variables, evt: Event, basketOp:BasketOp) {
        && 0 < v.keysInApron
        && v' == v.(keysInApron := v.keysInApron - 1)
        // An interaction between a customer and a barista is direct in this
        // model, not mediated by an asynchronous message.
        && basketOp == BasketOp(0)
    }

    ghost predicate CustomerReleasesKey(c: Constants, v: Variables, v': Variables, evt: Event, basketOp:BasketOp) {
        && v' == v.(keysInApron := v.keysInApron + 1)
        && basketOp == BasketOp(0)
    }

    //Baristas can drop keys into a common basket for others to pick up
    ghost predicate BaristaDropsKeyInBasket(c: Constants, v: Variables, v': Variables, evt: Event, basketOp:BasketOp) {
        && 0 < v.keysInApron
        && v' == v.(keysInApron := v.keysInApron - 1)
        && basketOp == BasketOp(1)
    }
    
    //Any barista may pick up a key from the basket
    ghost predicate BaristaTakesKeyFromBasket(c: Constants, v: Variables, v': Variables, evt: Event, basketOp:BasketOp) {
        && v' == v.(keysInApron := v.keysInApron + 1)
        && basketOp == BasketOp(-1)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, basketOp:BasketOp)
    {
        match evt {
            case Acquire => CustomerAcquiresKey(c, v, v', evt, basketOp)
            case Release => CustomerReleasesKey(c, v, v', evt, basketOp)
            case NoOp => BaristaDropsKeyInBasket(c, v, v', evt, basketOp) || BaristaTakesKeyFromBasket(c, v, v', evt, basketOp)
        }
    }

}

// The (trusted) model of the Basket.
// The Basket module models a means of communication among the baristas.
// Baristas can add keys to the basket (by providing a positive keyDelta)
// or remove keys from it (by providing a negative one).
module Basket {
    import opened UtilitiesLibrary
    import opened Types

    datatype Constants = Constants()
    datatype Variables = Variables(numKeysInBasket: nat)

    ghost predicate Init(c: Constants, v: Variables)
    {
        v.numKeysInBasket == 0
    }

    ghost predicate Next(c: Constants, v: Variables, v':Variables, basketOps: BasketOp)
    {
        && 0 <= v.numKeysInBasket + basketOps.keyDelta
        && v'.numKeysInBasket == v.numKeysInBasket + basketOps.keyDelta
    }
}

// The (trusted) model of the customer pool.
// Player 1 makes a promise to the system that clients cannot return
// more keys than they've acquired; this state machine enforces that
// assumption.
// In the physical world this protocol models, this assumption is
// enforced by the assumption that customers can't duplicate the physical keys.
module CustomerPool {
    import opened Events

    datatype Constants = Constants
    datatype Variables = Variables(keysHeldByAllClients: nat)

    ghost predicate Init(c: Constants, v: Variables) {
        && v.keysHeldByAllClients == 0
    }

    ghost predicate CustomerAcquiresKey(c: Constants, v: Variables, v': Variables) {
        // There's no enabling condition for acquiring keys.
        // If player 2 (the protocol) hands us one, we'll take it.
        && v'.keysHeldByAllClients == v.keysHeldByAllClients + 1
    }

    ghost predicate CustomerReleasesKey(c: Constants, v: Variables, v': Variables) {
        // The only job of this module is to keep track of how many keys the
        // customer pool is holding, so we don't give back more than we have.
        && 0 < v.keysHeldByAllClients
        && v'.keysHeldByAllClients == v.keysHeldByAllClients - 1
    }

    ghost predicate NoOpAction(c: Constants, v: Variables, v': Variables) {
        && v' == v
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case Acquire => CustomerAcquiresKey(c, v, v')
            case Release => CustomerReleasesKey(c, v, v')
            case NoOp => NoOpAction(c, v, v')
        }
    }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each host
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the Basket module.
module DistributedSystem {
    import opened Events
    import opened UtilitiesLibrary
    import opened Types
    import Host
    import CustomerPool
    import Basket

    datatype Constants = Constants(
        totalKeys: nat,
        hosts: seq<Host.Constants>,
        basket: Basket.Constants,
        customerPool: CustomerPool.Constants)
    {
        ghost predicate WF() {
            0 < |hosts|
        }

        ghost predicate ValidHostId(id: HostId) {
            id < |hosts|
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        // a shared basket where baristas drop keys for other baristas to pick up
        basket: Basket.Variables,
        customerPool: CustomerPool.Variables
        )
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && |hosts| == |c.hosts|
        }
    }

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Host.GroupInit(c.hosts, v.hosts, c.totalKeys)
        && Basket.Init(c.basket, v.basket)
        && CustomerPool.Init(c.customerPool, v.customerPool)
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, hostid: HostId, basketOp: BasketOp)
    {
        && v.WF(c)
        && v'.WF(c)
        && c.ValidHostId(hostid)
        && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], evt, basketOp)
        && Basket.Next(c.basket, v.basket, v'.basket, basketOp)
        && CustomerPool.Next(c.customerPool, v.customerPool, v'.customerPool, evt)
        // all other hosts UNCHANGED
        && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
    }

    // JayNF is pretty simple as there's only a single action disjunct
    datatype Step =
        | HostActionStep(hostid: HostId, basketOp: BasketOp)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostid, step.basketOp)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}

// This is the definition of the refinement obligation
abstract module RefinementTheorem {
    import opened Events
    import Spec
    import DistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
        requires v.WF(c)

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires DistributedSystem.Init(c, v)
        ensures Inv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
        requires DistributedSystem.Next(c, v, v', evt)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
}

// The RefinementProof module refines the abstract RefinementTheorem module. This means
// that it inherits all its functions and lemmas, along with their pre- and post-conditions.
// In the function/lemmas below, we mention the implied pre- and post-conditions for 
// reference, as a comment. 

module RefinementProof refines RefinementTheorem {
    import Host
    import Basket
    import opened Types

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
//        requires c.WF()
    {
/*{*/
        Spec.Constants(0)
/*}*/
    }

// Use the space below to define helper functions/lemmas for proving refinement 
/*{*//*}*/
    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
//        requires v.WF(c)
    {
/*{*/
        Spec.Variables(0)
/*}*/
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
/*{*/
        true
/*}*/
    }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
/*{*//*}*/
    }
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
//        requires DistributedSystem.Next(c, v, v', evt)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
/*{*//*}*/
    }
}
