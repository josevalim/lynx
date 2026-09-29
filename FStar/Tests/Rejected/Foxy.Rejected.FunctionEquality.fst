module Foxy.Rejected.FunctionEquality
// Logical function equality is a proposition; it is not executable equality.
let same (f:int -> Tot int) (g:int -> Tot int) : Tot bool = f = g
