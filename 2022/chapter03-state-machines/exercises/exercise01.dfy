//#title Coke Machine
//#desc The first state machine specification exercise: fill in actions.

// You are asked to define the state machine for a coke vending machine.
// The machine starts empty and has a maximum capacity of 7 cokes. 
// The machine should support the following actions:
// Purchase: dispense one coke from the machine
// Restock: add a number of cokes to the machine

datatype Constants = Constants(capacity:int)
datatype Variables = Variables(numCokes:int)

predicate Init(c:Constants, v:Variables) {
/*{*/
  true // Replace me
/*}*/
}

predicate Purchase(c:Constants, v:Variables, v':Variables) {
/*{*/
  true // Replace me
/*}*/
}

predicate Restock(c:Constants, v:Variables, v':Variables, numRestock:int) 
{
/*{*/
  true // Replace me
/*}*/
}

// Jay-Normal-Form: pack all the nondeterminism into a single object
datatype Step =
  | PurchaseStep
  | RestockStep(num: int)

predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
    case PurchaseStep => Purchase(c, v, v')
    case RestockStep(num) => Restock(c, v, v', num)
}

predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
} 

//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.

predicate Inv(c:Constants, v:Variables) {
    0 <= v.numCokes <= c.capacity
}

lemma SafetyProof() 
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && Next(c, v, v') 
        ensures Inv(c, v')
    {
        if(Purchase(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            assert Inv(c, v');
        }   
    }
}

lemma NonTrivialPurchase()
    ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes
{
    var c := Constants(7);
    var v := Variables(1);   
    var v' := Variables(0);   
    assert NextStep(c, v, v', PurchaseStep);
    assert Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes;
}

lemma NonTrivialRestock()
    ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes
{
    var c := Constants(7);
    var v := Variables(4);   
    var v' := Variables(7);   
    assert NextStep(c, v, v', RestockStep(3));
    assert Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes;
}


