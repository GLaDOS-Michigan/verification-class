//#title Maps. Set, Map and Sequence comprehensions.

predicate IsEven(x:int)
{
  x/2*2==x
}

lemma SetComprehension()
{
  // Here's how you define a "big" (perhaps unknown size, but finite) set:
  // Read it as "the set of values x such that (|) x is between 0 and 10 and is even."
  // (In general, it's "the set of value x such that predicate P(x) is true".)
  var modestEvens := set x | 0 <= x < 10 && IsEven(x);
  assert modestEvens == {/*{*/0,2,4,8/*}*/};
}

lemma Maps()
{
  // Map generic type, map literal syntax
  var doubleMap:map<int, int> := map[1:=2, 2:=4, 3:=6, 4:=8];

  assert doubleMap[3] == 6;

  var replaceMap := doubleMap[3 := 7];
  assert replaceMap[1] == 2;
  assert replaceMap[2] == 4;
  assert replaceMap[3] == /*{*/6/*}*/;
}

lemma MapComprehension()
{
  // Here's how you define a "big" (but finite-domain) map. Read it as
  // "The map with domain x such that 0<=x<5" (that is, domain is defined just like a set comprehension)
  // ..."and for which the value at [x] is 2*x" (the thing after :: is an expression of the value type).
  // This map is type-inferred to be map<int,int>.
  var doublyMap := map x | 0<=x<5 :: 2*x;
  assert doublyMap[1] == 2;
  assert doublyMap[4] == /*{*/4/*}*/;
}

lemma SeqComprehension()
{
  // The sequence comprehension syntax is, unfortunately, kinda hideous compared
  // to the set & map comprehensions. seq(N, f) is a function.
  //
  // N is the size of the output sequence (that is, |eventsInOrder| == 5).
  //
  // f is a function -- in this case an anonymous lambda -- that gives the value
  // at each index. The "i" before the "=>" is the parameter list of the lambda;
  // "i*2" is the expression body of the lambda function. The "requires 0<=i<5"
  // is a way to pass into the lambda the knowledge that seq() will only call
  // it with those particular values. It's not actually needed here (since the
  // expression i*2 works on all integers), but it's quite often necessary.
  var evensInOrder := seq(5, i requires 0<=i<5 => i*2);
  assert evensInOrder[2] == 4;
  assert evensInOrder == [/*{*/8,6,4,2,0/*}*/];
}

