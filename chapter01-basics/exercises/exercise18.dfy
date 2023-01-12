//#title FindMax
//#desc Loop invariants.

method FindMax(intSeq:seq<int>) returns (maxIndex:nat)
    requires |intSeq| > 0
    ensures maxIndex<|intSeq|
    ensures forall idx:nat | idx<|intSeq| :: intSeq[idx] <= intSeq[maxIndex]
{
    var count:nat := 0;
    maxIndex := 0;
    while(count < |intSeq|)
    /*{*/
        invariant true  // hint: you'll need three invariants
        invariant true
        invariant true
    /*}*/
    {
        if(intSeq[maxIndex] < intSeq[count]) {
            maxIndex := count;
        }
        count := count+1;
    }
}
