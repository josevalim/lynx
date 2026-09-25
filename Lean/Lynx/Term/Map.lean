module

public import Lynx.Term.Compare

/-!
We chose association lists over hash maps or trees because embedding maps of
terms recursively within `Term` complicates their equality, ordering, and
validity requirements. Every association list denotes a map without extra
client proofs. We also tried quotient lists, but they added complexity
throughout the implementation and proofs.

The first semantically equal key wins; `put` prepends and `merge` puts right
bindings first. Equality and ordering use `Term.exactCompare`, independently of
storage order. Retained shadowed bindings and slower traversal are acceptable
for our current focus on proof performance rather than runtime execution.
The Sets benchmarks track proof performance as this representation evolves.
-/
namespace Lynx.Term.Map

public abbrev Entries := List (Term × Term)

/-- Find a value using semantic key equality. -/
@[expose] public def find (q : Term) (xs : Entries) : Option Term :=
  (xs.find? fun e => decide (exactCompare q e.1 = .eq)).map Prod.snd

/-- Put a binding, shadowing any previous value for the key. -/
@[expose, simp] public def put (k v : Term) (xs : Entries) : Entries := (k,v) :: xs

/-- Right bindings win, including when equivalent keys have different representations. -/
@[expose, simp] public def merge (a b : Entries) : Entries := b ++ a

end Lynx.Term.Map
