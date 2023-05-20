//#title Struct (product) datatypes.

// Okay, but I know you won't settle for merely renaming some fancy type
// expression.  You actually want to define something new.

// Dafny has "algebraic" datatypes which capture both "struct"
// and (tagged) "union".
// First, structs:
datatype Point = PointCtor(x:int, y:int)

// You could alternatively write this as:
//   datatype Point = Point(x:int, y:int)
// The first "Point" is the type name, the second is the constructor name. When
// the type has only one constructor, it's conventional to give them the same
// name since the language can distinguish the two uses from context.

/*{*/
ghost function subtractPoints(tip:Point, tail:Point) : Point
{
  PointCtor(tip.x - tail.x, tip.y - tail.x)
}
/*}*/

lemma PointArithmetic()
{
  var a := PointCtor(1,13);
  var b := PointCtor(2,7);

  // NB Points (and every other `datatype`) are mathematical, immutable
  // objects, so the one we get back from the function must be equal
  // (identical) to the one we construct manually. There's no implicit
  // user-overridable Equals() method; these are platonic mathematical objects.

  // This exercise is a little harder than the previous ones; take a moment
  // to investigate it carefully!
  assert subtractPoints(a, b) == PointCtor(-1, 6);
}


