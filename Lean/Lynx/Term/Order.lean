module

public import Lynx.Term.DataTypes
public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic

public section

namespace Lynx.Result
open Lean.Order

/-- Partial computations approximate a result by `exhausted` or return it exactly.
An explicit bottom makes recursive calls under a bind usable in fixed points. -/
noncomputable instance resultCCPO : CCPO (Result α) :=
  inferInstanceAs (CCPO (FlatOrder (Result.exhausted : Result α)))

/-- Postconditions on successful returns hold vacuously at the bottom. -/
theorem admissible_success (post : α → Prop) :
    admissible (fun computation : Result α => ∀ value, computation = .ok value → post value) := by
  apply admissible_flatOrder
  change ∀ value, (Result.exhausted : Result α) = .ok value → post value
  simp

theorem bind_mono_left {left right : Result α} (next : α → Result β)
    (below : PartialOrder.rel left right) :
    PartialOrder.rel (left >>= next) (right >>= next) := by
  change FlatOrder.rel left right at below
  cases below with
  | bot => exact FlatOrder.rel.bot
  | refl => exact FlatOrder.rel.refl

theorem bind_mono_pure (computation : Result α) (pure : IsPure computation)
    {left right : α → Result β} (below : ∀ value, PartialOrder.rel (left value) (right value)) :
    PartialOrder.rel (computation >>= left) (computation >>= right) := by
  cases computation <;> simp [IsPure] at pure
  · exact below _
  · exact PartialOrder.rel_refl

theorem tryWith_mono_pure (computation : Result α) (pure : IsPure computation)
    {left right : α → Result β} {leftError rightError : Exception → Result β}
    (below : ∀ value, PartialOrder.rel (left value) (right value))
    (errors : ∀ exception, PartialOrder.rel (leftError exception) (rightError exception)) :
    PartialOrder.rel (tryWith computation left leftError) (tryWith computation right rightError) := by
  cases computation <;> simp [IsPure] at pure
  · simpa using below _
  · simpa using errors _

theorem bind_eq_ok (computation : Result α) (next : α → Result β) (value : β) :
    (computation >>= next) = .ok value ↔
      ∃ input, computation = .ok input ∧ next input = .ok value := by
  cases computation <;> simp

end Lynx.Result
