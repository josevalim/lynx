module Foxy.Rejected.RecursiveClosure
// This representation must fail the strict positivity check.
noeq type term =
| Integer : int -> term
| Closure : (list term -> Tot term) -> term
