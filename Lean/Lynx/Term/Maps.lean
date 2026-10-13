module

public import Lynx.Term.Compare

public section

namespace Lynx.Term

/-- Collect map values in key order, including repeated keys. Return an empty
Lean list if the input is not a map or any key is missing. The clause decoder
uses this for nonempty key lists; empty map patterns match the map constructor. -/
@[expose] def getMapKeys (keys : List Term) (input : Term) : List Term :=
  match input with
  | .map entries =>
    (keys.mapM fun key =>
      (entries.find? fun entry => decide (exactCompare key entry.1 = .eq)).map Prod.snd).getD []
  | _ => []

@[simp] theorem getMapKeys_nil (input : Term) : getMapKeys [] input = [] := by
  cases input <;> rfl

private theorem mapM_length (lookup : α → Option β) (keys : List α)
    (values : List β) (returned : keys.mapM lookup = some values) :
    values.length = keys.length := by
  induction keys generalizing values with
  | nil =>
    simp [Pure.pure] at returned
    subst values
    rfl
  | cons key rest ih =>
    cases head : lookup key with
    | none => simp [head, Bind.bind, Option.bind] at returned
    | some value =>
      cases tail : rest.mapM lookup with
      | none => simp [head, tail, Bind.bind, Option.bind] at returned
      | some remaining =>
        simp [head, tail, Bind.bind, Pure.pure, Option.bind] at returned
        subst values
        simpa using ih remaining tail

/-- A nonempty result contains exactly one value per requested key. -/
theorem getMapKeys_arity (keys : List Term) (input : Term)
    (nonempty : getMapKeys keys input ≠ []) :
    (getMapKeys keys input).length = keys.length := by
  cases input <;> simp only [getMapKeys] at nonempty ⊢
  all_goals try contradiction
  rename_i entries
  let lookup := fun key =>
    (entries.find? fun entry => decide (exactCompare key entry.1 = .eq)).map Prod.snd
  change (keys.mapM lookup).getD [] ≠ [] at nonempty
  change ((keys.mapM lookup).getD []).length = keys.length
  cases found : keys.mapM lookup with
  | none => simp [found] at nonempty
  | some values =>
    simp only [Option.getD_some]
    exact mapM_length lookup keys values found

end Lynx.Term
