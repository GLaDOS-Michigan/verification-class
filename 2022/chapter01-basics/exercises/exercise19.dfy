//#title IsSeqSorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsSeqSorted(intSeq:seq<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intSeq[..])
{
  /*{*/
  return true;
  /*}*/
}
