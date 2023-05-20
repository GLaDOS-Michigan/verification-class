module Types {

  // TODO: should we ask students to define these?
  datatype Event =
    | Get(key: int, value: int)
    | Put(key: int, value: int)
    | NoOp()
}

