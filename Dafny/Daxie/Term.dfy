module Terms {
  type FiniteFloat = value: fp64 | value.IsFinite witness 0.0

  datatype Term =
    Integer(integer: int)
    | Float(float: FiniteFloat)
    | Atom(atom: string)
    | Tuple(elements: seq<Term>)
    | Nil
    | Cons(head: Term, tail: Term)

  datatype Result = Ok(value: Term) | Error(reason: Term)

  function Boolean(value: bool): Term {
    Atom(if value then "true" else "false")
  }
}
