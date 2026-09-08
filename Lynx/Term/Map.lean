import Lynx.Term.Compare

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
def put (k v : Term) (xs : Entries) : Entries := (k,v) :: xs

/-- Right bindings win, including when equivalent keys have different representations. -/
def merge (a b : Entries) : Entries := b ++ a

@[simp] private theorem findEntry_cons (k v : Term) (xs : Entries) (q : Term) :
    findEntry ((k,v) :: xs) q =
      if compare q k = .eq then some (k,v) else findEntry xs q := by
  by_cases h : compare q k = .eq <;> simp [findEntry, List.find?, h]

@[simp] private theorem findEntry_nil (q : Term) : findEntry [] q = none := rfl
@[simp] theorem find_nil (q : Term) : find q [] = none := rfl

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

private theorem findEntry_self {xs : Entries} {q : Term} {e : Term × Term}
    (h : findEntry xs q = some e) : findEntry xs e.1 = some e := by
  have accepted : decide (compare q e.1 = .eq) = true :=
    List.find?_some (p := fun (e : Term × Term) => decide (compare q e.1 = .eq)) h
  have key : compare q e.1 = .eq := of_decide_eq_true accepted
  simpa only [findEntry, Std.TransCmp.congr_left key] using h

/-- A predicate on effective stored bindings only, excluding shadowed entries. -/
def All (predicate : Term → Term → Prop) (xs : Entries) : Prop :=
  ∀ q k v, findEntry xs q = some (k,v) → predicate k v

/-- Visit the winning binding for each stored key. Repeated visits are harmless
for these pure predicates; shadowed values are never passed to the predicate. -/
def all (xs : Entries) (predicate : Term → Term → Bool) : Bool :=
  xs.all fun (k,_) => match findEntry xs k with
    | some (key,value) => predicate key value
    | none => true

@[simp] theorem all_iff (xs : Entries) (predicate : Term → Term → Bool) :
    all xs predicate = true ↔ All (fun k v => predicate k v = true) xs := by
  simp only [all, List.all_eq_true]
  constructor
  · intro h q k v found
    have mem := List.mem_of_find?_eq_some found
    have self := findEntry_self found
    simpa [self] using h (k,v) mem
  · intro h ⟨k,v⟩ _
    cases found : findEntry xs k with
    | none => rfl
    | some e => exact h k e.1 e.2 found

@[simp] theorem all_empty (predicate : Term → Term → Prop) : All predicate [] := by
  intro q k v h; cases h

@[simp] theorem all_put (predicate : Term → Term → Prop) (xs : Entries) (k v : Term)
    (h : All predicate xs) (hv : predicate k v) : All predicate (put k v xs) := by
  intro q a b found
  simp only [findEntry_put] at found
  split at found
  · cases found; exact hv
  · exact h q a b found

@[simp] theorem all_merge (predicate : Term → Term → Prop) (a b : Entries)
    (ha : All predicate a) (hb : All predicate b) : All predicate (merge a b) := by
  intro q k v found
  rw [findEntry_merge] at found
  cases h : findEntry b q with
  | none => exact ha q k v (by simpa [h] using found)
  | some e => simp only [h] at found; cases found; exact hb q k v h

/-- Matching effective values suffice for semantic map equality. -/
theorem equivalent_of_find (a b : Entries)
    (h : ∀ q, Option.Rel Equivalent (find q a) (find q b)) :
    Equivalent (.map a) (.map b) := by
  exact map_equivalent_of_lookup a b h

theorem all_find (predicate : Term → Prop) {xs : Entries}
    (h : All (fun _ v => predicate v) xs) {q v : Term} (found : find q xs = some v) :
    predicate v := by
  unfold find at found
  cases raw : findEntry xs q with
  | none => simp [raw] at found
  | some e =>
    simp only [raw, Option.map_some, Option.some.injEq] at found
    exact found ▸ h q e.1 e.2 raw

/-- Common-value maps commute semantically, including maps with shadowed entries. -/
private theorem merge_comm_of_equivalent_constant (value : Term) (a b : Entries)
    (ha : All (fun _ v => compare v value = .eq) a)
    (hb : All (fun _ v => compare v value = .eq) b) :
    compare (.map (merge a b)) (.map (merge b a)) = .eq := by
  change Equivalent (.map (merge a b)) (.map (merge b a))
  apply equivalent_of_find
  intro q
  simp only [find_merge]
  cases ea : find q a <;> cases eb : find q b <;> simp_all [Equivalent]
  exact Std.TransCmp.eq_trans (all_find _ hb eb) (Std.OrientedCmp.eq_symm (all_find _ ha ea))

@[simp] theorem merge_comm_of_constant (value : Term) (a b : Entries)
    (ha : All (fun _ v => v = value) a) (hb : All (fun _ v => v = value) b) :
    compare (.map (merge a b)) (.map (merge b a)) = .eq := by
  apply merge_comm_of_equivalent_constant value a b
  · intro q k v h; rw [ha q k v h]; exact compare_self value
  · intro q k v h; rw [hb q k v h]; exact compare_self value

end Lynx.Term.Map
