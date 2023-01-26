//#title Merge Sort
//#desc More specification practice.

// Implement a merge sort that guarantees the result is sorted.
// merge() should merge its two sorted inputs into a sorted output.
// merge_sort picks a pivot, recursively merge_sort()s the subsequences,
// and then uses merge() to put them back together. We've provided
// signatures for merge and merge_sort to get you started.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

/*{*//*}*/
method merge_sort(input:seq<int>) returns (output:seq<int>)
/*{*/
  ensures true  // Replace me
/*}*/
{
/*{*/
  // Supply the body.
/*}*/
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
/*{*/
  ensures true  // Replace me
/*}*/
{
/*{*/
  // Supply the body.
/*}*/
}


