module

public import Lynx.Term
public import Lynx.Term.Map
public import Lynx.Pure

public section

namespace Erlang.maps
open Lynx
open Term.Map

#lynx_pure @[expose] def «new/0» : Result := .ok Term.emptyMap

#lynx_pure @[expose] def «get/2» (key input : Term) : Result :=
  match input with
  | .map entries =>
    match find key entries with
    | some v => .ok v
    | none => .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

#lynx_pure @[expose] def «put/3» (key value input : Term) : Result :=
  match input with
  | .map entries => .ok (.map (put key value entries))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

#lynx_pure @[expose] def «merge/2» (left right : Term) : Result :=
  match left, right with
  | .map a, .map b => .ok (.map (merge a b))
  | .map _, _ => .error (.error (.tuple #[.atom "badmap", right]))
  | _, _ => .error (.error (.tuple #[.atom "badmap", left]))

/-- Lookup after merging prefers the right map, falling back to the left
when the key is absent. -/
theorem get_merge (key : Term) (left right : List (Term × Term)) :
    («merge/2» (.map left) (.map right) >>= «get/2» key) =
      match «get/2» key (.map right) with
      | .error _ => «get/2» key (.map left)
      | result => result := by
  simp only [«merge/2», merge, Result.ok_bind, «get/2», find, List.find?_append,
    Option.map_or]
  cases (right.find? fun e => decide (Term.exactCompare key e.1 = .eq)).map Prod.snd <;> rfl

/-- Maps with identical lookup results are semantically equal. -/
theorem compare_eq_of_get (left right : List (Term × Term))
    (h : ∀ key, «get/2» key (.map left) = «get/2» key (.map right)) :
    Term.compare (.map left) (.map right) = .eq := by
  apply Term.map_compare_eq_of_lookup
  intro key
  have equal := h key
  simp only [«get/2»] at equal
  change Option.Rel _ (find key left) (find key right)
  cases ha : find key left <;> cases hb : find key right <;> simp_all

end Erlang.maps
