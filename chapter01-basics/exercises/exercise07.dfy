//#title Sequences: Literals, indexing

lemma ExperimentsWithSequences()
{
  // [x,y,z] is a literal sequence; this one is a seq<int>.
  var fibo := [1,1,2,3,5,8,13,21,34];
  // Index into a sequence.
  assert fibo[4] == 5;

  // Sequences have cardinality (and hence are always finite length).
  assert |fibo| == 9;
  assert fibo[0] == 1;
  assert fibo[8] == 34;
  assert fibo[/*{*/9/*}*/] == 21;
}
