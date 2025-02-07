//#title Crawler quadrants
//#desc Introduction to inductive invariants
//#desc A more advanced crawler state machine

// You are asked to write the state machine, safety property and inductive invariant 
// for the following crawler, which moves through the X-Y Cartesian space.
// The crawler can take three types of actions: it can move one step in its current 
// vertical direction; it can move one step in its current horizontal direction; or
// it can warp. A horizontal warp would take it to a position that mirrors its current 
// position on the Y-axis (e.g. (1,5) would go to (-1,5)), while also flipping its 
// horizontal direction (i.e. from left to right or vice versa). Similarly, a vertical 
// warp would take it to a position that mirrors its current position on the X-axis 
// (e.g. (1,5) would go to (1,-5)), while also flipping its vertical direction (i.e. 
// from up to down or vice versa).

// The crawler starts in position (5,5) and with a horizontal direction of "right" and
// a vertical direction of "up".

// The desired safety property is that the crawler should always be at least 5 points 
// away from both axes.

/*{*/  
// Editable space, in case you need any definitions
/*}*/

datatype Variables = Variables(
/*{*/    
/*}*/
)

ghost predicate Init(v: Variables) {
/*{*/    
    true // Replace me
/*}*/
}

// Define your actions here

/*{*/    
/*}*/

ghost predicate Next(v: Variables, v': Variables) {
/*{*/    
    true // Replace me
/*}*/
}

/*{*/    
// Editable space, in case you need any definitions
/*}*/

ghost predicate Safety(v: Variables) {
/*{*/    
    false // Replace me
/*}*/
}

ghost predicate Inv(v: Variables) {
/*{*/    
    true // Probably not strong enough!
/*}*/    
}

lemma InvImpliesSafety(v: Variables) 
    requires Inv(v)
    ensures Safety(v)
{
/*{*/
/*}*/     
}

lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
{
/*{*/
/*}*/     
}

lemma NextPreservesInv(v: Variables, v': Variables) 
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
{
/*{*/
/*}*/     
}

