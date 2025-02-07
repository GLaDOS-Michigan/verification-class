module Types {

  datatype Event =
    | Get(key: int, value: int)
    | Put(key: int, value: int)
    | NoOp()
}

