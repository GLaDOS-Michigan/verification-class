//#title Sequences: Slices

lemma ExperimentsWithSequences()
{
  var fibo := [1,1,2,3,5,8,13,21,34];

  // A slice of a sequence is a sequence.
  // The left argument is inclusive, the right exclusive.
  assert fibo[2..4] == [2,3];

  // You can omit either endpoint to refer to the beginning or end of the
  // sequence.
  assert fibo[..3] == [1,1,2];
  assert fibo[7..] == [21,34];

  assert fibo[5..6] == /*{*/8/*}*/;
}
