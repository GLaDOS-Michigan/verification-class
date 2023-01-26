//#title Sequences: types, cardinality

lemma ExperimentsWithSequences()
{
  var fibo := [1,1,2,3,5,8,13,21,34];

  // The type of fibo is seq<int>.
  // Here, we explicitly declare the type of `copy`. In previous examples, the
  // type has always been inferred by the compiler. I just wanted you to see
  // what it was inferring.
  var copy:seq<int> := fibo;

  // You can, of course, have a seq of other stuff.
  var seqOfSets:seq<set<int>> := [{0}, {0,1}, {0,1,2}];

  var whatsMyProblem := [0, /*{*/1, false/*}*/];

  // |expr| below is sequence-length
  assert |seqOfSets| == 3;
  // Type checking means the |expr| below is a set-cardinality operator.
  assert |seqOfSets[1]| == /*{*/3/*}*/;
}
