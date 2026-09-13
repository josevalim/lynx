module

public import Lynx.Term.Compare
import all Lynx.Term.Compare

public section

/-!
We chose association lists over hash maps or trees because embedding maps of
terms recursively within `Term` complicates their equality, ordering, and
validity requirements. Every association list denotes a map without extra
client proofs. We also tried quotient lists, but they added complexity
throughout the implementation and proofs.

The first semantically equal key wins; `put` prepends and `merge` puts right
bindings first. Equality and ordering use `Term.compare`, independently of
storage order. Retained shadowed bindings and slower traversal are acceptable
for our current focus on proof performance rather than runtime execution.
The Sets benchmarks track proof performance as this representation evolves.
-/
namespace Lynx.Term.Map

abbrev Entries := List (Term × Term)

/-- Return the actual stored binding, using semantic equality for the query key. -/
private def findEntry (xs : Entries) (q : Term) : Option (Term × Term) :=
  xs.find? fun e => decide (compare q e.1 = .eq)

/-- Find a value using semantic key equality. -/
def find (q : Term) (xs : Entries) : Option Term := (findEntry xs q).map Prod.snd

/-- Put a binding, shadowing any previous value for the key. -/
@[expose] def put (k v : Term) (xs : Entries) : Entries := (k,v) :: xs

/-- Right bindings win, including when equivalent keys have different representations. -/
@[expose] def merge (a b : Entries) : Entries := b ++ a

@[simp] private theorem findEntry_cons (k v : Term) (xs : Entries) (q : Term) :
    findEntry ((k,v) :: xs) q =
      if compare q k = .eq then some (k,v) else findEntry xs q := by
  by_cases h : compare q k = .eq <;> simp [findEntry, List.find?, h]

@[simp] private theorem findEntry_nil (q : Term) : findEntry [] q = none := rfl
@[simp] private theorem find_nil (q : Term) : find q [] = none := rfl

@[simp] private theorem findEntry_put (xs : Entries) (k v q : Term) :
    findEntry (put k v xs) q =
      if compare q k = .eq then some (k,v) else findEntry xs q := by
  exact findEntry_cons k v xs q

@[simp] theorem find_put (xs : Entries) (k v q : Term) :
    find q (put k v xs) =
      if compare q k = .eq then some v else find q xs := by
  by_cases h : compare q k = .eq <;> simp [find, h]

@[simp] private theorem findEntry_merge (a b : Entries) (q : Term) :
    findEntry (merge a b) q = (findEntry b q).or (findEntry a q) := by
  exact List.find?_append

@[simp] theorem find_merge (a b : Entries) (q : Term) :
    find q (merge a b) = (find q b).or (find q a) := by
  simp only [find, findEntry_merge]
  exact Option.map_or

@[simp] theorem merge_empty (a : Entries) : merge a [] = a := rfl
@[simp] theorem empty_merge (a : Entries) : merge [] a = a := List.append_nil _
@[simp] theorem merge_assoc (a b c : Entries) : merge (merge a b) c = merge a (merge b c) :=
  (List.append_assoc _ _ _).symm

/-- Matching effective values suffice for semantic map equality. -/
theorem equivalent_of_find (a b : Entries)
    (h : ∀ q, Option.Rel Equivalent (find q a) (find q b)) :
    Equivalent (.map a) (.map b) := by
  exact map_equivalent_of_lookup a b h

end Lynx.Term.Map
