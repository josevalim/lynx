module

public import Lynx.Term
public import Lynx.Pure

public section

namespace Erlang.maps
open Lynx

#lynx_pure @[expose] def «new/0» : Result := .ok (Term.map [])

#lynx_pure @[expose] def «get/2» (key input : Term) : Result :=
  match input with
  | .map entries =>
    match (entries.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd with
    | some v => .ok v
    | none => .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

#lynx_pure @[expose] def «put/3» (key value input : Term) : Result :=
  match input with
  | .map entries => .ok (.map ((key, value) :: entries))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

#lynx_pure @[expose] def «merge/2» (left right : Term) : Result :=
  match left, right with
  | .map a, .map b => .ok (.map (b ++ a))
  | .map _, _ => .error (.error (.tuple #[.atom "badmap", right]))
  | _, _ => .error (.error (.tuple #[.atom "badmap", left]))

/-- Lookup after merging prefers the right map, falling back to the left
when the key is absent. -/
theorem get_merge (key : Term) (left right : List (Term × Term)) :
    («merge/2» (.map left) (.map right) >>= «get/2» key) =
      match «get/2» key (.map right) with
      | .error _ => «get/2» key (.map left)
      | result => result := by
  simp only [«merge/2», Result.ok_bind, «get/2», List.find?_append, Option.map_or]
  cases (right.find? fun e => decide (Term.exactCompare key e.1 = .eq)).map Prod.snd <;> rfl

/-- Maps with identical lookup results are semantically equal. -/
theorem compare_eq_of_get (left right : List (Term × Term))
    (h : ∀ key, «get/2» key (.map left) = «get/2» key (.map right)) :
    Term.compare (.map left) (.map right) = .eq := by
  apply Term.map_compare_eq_of_lookup
  intro key
  have equal := h key
  simp only [«get/2»] at equal
  change Option.Rel _
    ((left.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd)
    ((right.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd)
  cases ha : (left.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd <;>
    cases hb : (right.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd <;> simp_all

/-- Map shape is the only requirement; keys and values may be arbitrary terms. -/
theorem get_after_put (m k v : Term)
    (hm : ∃ entries, m = .map entries) :
    («put/3» k v m >>= «get/2» k) = .ok v := by
  obtain ⟨entries, rfl⟩ := hm
  simp [«put/3», «get/2»]

/-- Right-biased map merge is associative. -/
theorem merge_associative (a b c : Term)
    (ha : ∃ entries, a = .map entries)
    (hb : ∃ entries, b = .map entries)
    (hc : ∃ entries, c = .map entries) :
    («merge/2» a b >>= fun ab => «merge/2» ab c) =
      («merge/2» b c >>= «merge/2» a) := by
  obtain ⟨left, rfl⟩ := ha
  obtain ⟨middle, rfl⟩ := hb
  obtain ⟨right, rfl⟩ := hc
  simp [«merge/2»]

end Erlang.maps
