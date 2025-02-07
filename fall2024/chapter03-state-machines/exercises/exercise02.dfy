//#title Dining Philosophers
//#desc A more challenging state machine: define the state datatype.

// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table with N chairs.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).
//
// (Nota bene: The dining philosophers problem is used to illustrate deadlocks
// and deadlock-freedom. We're not doing any of that here, just using the
// example to teach you to set up a state machine model.)

datatype Constants = Constants(tableSize:nat)
{
  // An initial predicate to define well-formed constants.
  ghost predicate WellFormed() {
      && 0 < tableSize
  }
}


/*{*/
/*}*/
// Define all the relevant state in this datatype.
/*{*/
datatype Variables = Variables()
{
  ghost predicate WellFormed(c: Constants) {
    && c.WellFormed()
  }
}
/*}*/

ghost predicate Init(c:Constants, v:Variables) {
/*{*/
  true  // Replace me
/*}*/
}

/*{*/
/*}*/

// Philosopher with index philosopherIndex acquires left chopstick
ghost predicate AcquireLeft(c:Constants, v:Variables, v':Variables, philosopherIndex:nat) {
/*{*/
  true  // Replace me
/*}*/
}

// Philosopher with index philosopherIndex acquires right chopstick
ghost predicate AcquireRight(c:Constants, v:Variables, v':Variables, philosopherIndex:nat) {
/*{*/
  true  // Replace me
/*}*/
}

// Philosopher with index philosopherIndex releases both chopsticks
ghost predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, philosopherIndex:nat) {
/*{*/
  true  // Replace me
/*}*/
}

datatype Step =
/*{*/
  Step()  // Replace me
/*}*/

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
/*{*/
  case Step => false  // Replace me
/*}*/
}

ghost predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

// This predicate should be true if and only if no philosopher holds a
// chopstick.
// Since you defined the Variables state, you must define this predicate in
// those terms. Avoid using existential quantifiers.
ghost predicate NoSticksAcquired(c:Constants, v: Variables)
  requires v.WellFormed(c)
{
/*{*/
  true
/*}*/
}

// Change this predicate to be true if and only if philosopher
// `philosopherIndex` holds both of their chopsticks.
// Since you defined the Variables state, you must define this predicate in
// those terms. Avoid using existential quantifiers.
ghost predicate BothSticksAcquired(c:Constants, v: Variables, philosopherIndex: nat)
  requires philosopherIndex < c.tableSize
  requires v.WellFormed(c)
{
/*{*/
  true
/*}*/
}

// Show that, in the Init state, no philosopher has chopsticks.
lemma InitProperty(c:Constants, v: Variables, philosopherIndex:nat)
  requires Init(c, v)
  ensures NoSticksAcquired(c, v)
{
  /*{*/
  /*}*/
}


// Show a behavior that evolves from the init state to one where a philosopher
// has completed acquiring both chopsticks.
lemma PseudoLiveness(c:Constants, philosopherIndex:nat) returns (behavior:seq<Variables>)
    requires c.tableSize == 3
    requires philosopherIndex == 1
    ensures 0 < |behavior|  // precondition for index operators below
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1]) // Behavior satisfies your state machine
    ensures behavior[0].WellFormed(c) // precondition for calling NoSticksAcquired
    ensures Init(c, behavior[0])
    ensures behavior[|behavior|-1].WellFormed(c) // precondition for calling BothSticksAcquired
    ensures BothSticksAcquired(c, behavior[|behavior|-1], philosopherIndex)  // Behavior ultimately achieves acquisition for philosopherIndex
{
/*{*/
/*}*/
}
