namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences of flat types, on points of values. -/

theorem lookup_fold {L R O : List (Term × Term)} {g : Term → Term → Term → Term}
    (lookO : ∀ q, mapLookup O q =
      match (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | some e => (mapLookup L e.1).bind fun v₁ => if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none
      | none => mapLookup L q) (name : String) :
    mapLookup O (.atom name) = match mapLookup R (.atom name) with
      | some y => (mapLookup L (.atom name)).bind fun x =>
          if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else none
      | none => mapLookup L (.atom name) := by
  rw [lookO, find_atom]
  cases mapLookup R (.atom name) <;> rfl

end Elixir.STTDescrProofsTest
