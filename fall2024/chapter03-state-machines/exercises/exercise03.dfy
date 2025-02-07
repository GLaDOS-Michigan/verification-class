//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

datatype Constants = Constants(
/*{*/ // You define this ...
/*}*/
) {
  ghost predicate WellFormed() { true }
/*{*/
/*}*/
}

/*{*/
/*}*/

datatype Variables = Variables(
/*{*/ // You define this ...
/*}*/
) {
  ghost predicate WellFormed(c: Constants) {
/*{*/
    true
/*}*/
  }
}

ghost predicate Init(c:Constants, v:Variables) {
  && v.WellFormed(c)
/*{*/
  && true  // Replace me
/*}*/
}

/*{*/
/*}*/
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
/*{*/
  | SomeStep(somearg: int)   // Replace me
/*}*/

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
/*{*/
  case SomeStep(somearg) => false  // Replace me
/*}*/
}

ghost predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(c:Constants, v:Variables) {
/*{*/
  false  // Replace me
/*}*/
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(c: Constants, v: Variables, clientIndex: nat)
  requires v.WellFormed(c)
{
/*{*/
  false  // Replace me
/*}*/
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (c: Constants, behavior:seq<Variables>)
    requires clientA == 2
    requires clientB == 0
    ensures 0 < |behavior|  // precondition for index operators below
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1]) // Behavior satisfies your state machine
    ensures forall i | 0 <= i < |behavior| :: Safety(c, behavior[i]) // Behavior always satisfies the Safety predicate
    ensures behavior[0].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[0], clientA)
    ensures behavior[|behavior|-1].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[|behavior|-1], clientB)
{
/*{*/
/*}*/
}

