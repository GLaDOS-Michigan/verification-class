//#desc Library for exercises 12 & 14

// This is tagged union, a "sum" datatype.
datatype Direction = North() | East() | South() | West()

function TurnRight(direction:Direction) : Direction
{
  // This function introduces two new bits of syntax.
  // First, the if-else expression: if <bool> then T else T
  // Second, the element.Ctor? built-in predicate, which tests whether
  // the datatype `element` was built by `Ctor`.
  if direction.North?
    then East
  else if direction.East?
    then South
  else if direction.South?
    then West
  else  // By elimination, West!
    North
}

lemma Rotation()
{
  assert TurnRight(North) == East;
}

function TurnLeft(direction:Direction) : Direction
{
  // Another nice way to take apart a datatype element is with match-case
  // construct. Each case argument is a constructor; each body must be of the
  // same type, which is the type of the entire `match` expression.
  match direction {
    case North => West
    case West => South
    case South => East  // Try changing "East" to 7.
    case East => North
  }
}

