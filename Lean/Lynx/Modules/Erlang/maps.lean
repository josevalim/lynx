module

public import Lynx.Term

public section

namespace Erlang.maps
open Lynx

@[expose] def «new/0» : Except Exception Term := .ok (Term.map [])

@[expose] def «get/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    match (entries.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd with
    | some v => .ok v
    | none => .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «put/3» (key value input : Term) : Except Exception Term :=
  match input with
  | .map entries => .ok (.map ((key, value) :: entries))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «update/3» (key value input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    if (entries.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).isSome then
      .ok (.map ((key, value) :: entries))
    else
      .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

/-- Later pairs take precedence, so they shadow earlier ones. -/
@[expose] def «from_list/1» (list : Term) : Except Exception Term :=
  match Term.pairList? list with
  | some entries => .ok (.map entries.reverse)
  | none => .error (.error (.atom "badarg"))

@[expose] def «merge/2» (left right : Term) : Except Exception Term :=
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
  simp only [«merge/2», Except.ok_bind, «get/2», List.find?_append, Option.map_or]
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

/-- Updating a present key has the same result as putting it. -/
@[simp] theorem update_eq_put_of_get (m k v old : Term)
    (present : «get/2» k m = .ok old) :
    «update/3» k v m = «put/3» k v m := by
  cases m <;> simp [«get/2»] at present
  rename_i entries
  cases found : entries.find? (fun entry => decide (Term.exactCompare k entry.1 = .eq)) <;>
    simp_all [«update/3», «put/3»]

/-- A missing key raises badkey. -/
@[simp] theorem update_missing (entries : List (Term × Term)) (k v : Term)
    (missing : «get/2» k (.map entries) = .error (.error (.tuple #[.atom "badkey", k]))) :
    «update/3» k v (.map entries) = .error (.error (.tuple #[.atom "badkey", k])) := by
  cases found : entries.find? (fun entry => decide (Term.exactCompare k entry.1 = .eq)) <;>
    simp [«get/2», «update/3», found] at missing ⊢

/-- Reading the updated key returns its new value. -/
theorem get_after_update (m k v old : Term) (present : «get/2» k m = .ok old) :
    («update/3» k v m >>= «get/2» k) = .ok v := by
  rw [update_eq_put_of_get m k v old present]
  cases m <;> simp [«get/2»] at present
  apply get_after_put
  exact ⟨_, rfl⟩

/-- Putting a distinct key preserves lookup. -/
theorem get_after_put_other (entries : List (Term × Term)) (key other value : Term)
    (distinct : Term.exactCompare other key ≠ .eq) :
    («put/3» key value (.map entries) >>= «get/2» other) = «get/2» other (.map entries) := by
  simp [«put/3», «get/2», distinct]

/-- Updating a present key preserves lookup at distinct keys. -/
theorem get_after_update_other (entries : List (Term × Term)) (key other value old : Term)
    (present : «get/2» key (.map entries) = .ok old)
    (distinct : Term.exactCompare other key ≠ .eq) :
    («update/3» key value (.map entries) >>= «get/2» other) = «get/2» other (.map entries) := by
  rw [update_eq_put_of_get (.map entries) key value old present]
  exact get_after_put_other entries key other value distinct

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
