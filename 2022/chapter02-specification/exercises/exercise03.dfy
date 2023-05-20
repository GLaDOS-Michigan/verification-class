//#title Binary search
//#desc More specification practice

datatype Option<T> = Some(v: T) | None

predicate sorted(s: seq<int>) {
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

function BinarySearch(s: seq<int>, x: int): Option<nat> {
  /*{*/
  if |s| == 0 then None
  else (var mid := |s|/2;
        None // replace this with the recursive implementation
       )
  /*}*/
}

predicate SearchSpec(s: seq<int>, x: int, res: Option<nat>) {
  res.Some? ==>
    && res.v < |s|
    && s[res.v] == x
}

// Here's a specification and proof
lemma BinarySearch_ok(s: seq<int>, x: int)
  requires sorted(s)
  ensures SearchSpec(s, x, BinarySearch(s, x))
{
}

/*{*/
// We will talk about this specification and proof in class
/*}*/