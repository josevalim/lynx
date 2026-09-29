module Lists {
  datatype List<T> = Empty | Link(head: T, tail: List<T>)

  function Append<T>(left: List<T>, right: List<T>): List<T>
    decreases left
  {
    match left
    case Empty => right
    case Link(head, tail) => Link(head, Append(tail, right))
  }

  function Length<T>(xs: List<T>): nat
    decreases xs
  {
    match xs
    case Empty => 0
    case Link(_, tail) => 1 + Length(tail)
  }
}
