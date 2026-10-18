module

public import Lynx.Term.DataTypes
public import Lynx.Term.Except
public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic

public section

namespace Lynx.Order
open Lean.Order

/-- Public pointwise interface for the function order used by fixed points. -/
theorem rel_pi {ι : Sort u} {β : ι → Sort v} [∀ i, PartialOrder (β i)]
    (left right : ∀ i, β i) :
    PartialOrder.rel left right ↔ ∀ i, PartialOrder.rel (left i) (right i) := Iff.rfl

/-- Public componentwise interface for mutually recursive fixed points. -/
theorem rel_pprod {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β]
    (left right : α ×' β) : PartialOrder.rel left right ↔
      PartialOrder.rel left.1 right.1 ∧ PartialOrder.rel left.2 right.2 := Iff.rfl

end Lynx.Order

namespace Lynx.Result
open Lean.Order

/-- Partial computations approximate a result by not returning, or return it
exactly. An explicit bottom makes recursive calls under a bind usable in fixed points. -/
noncomputable instance resultCCPO : CCPO (Result α) :=
  inferInstanceAs (CCPO (FlatOrder (Result.error .exhausted : Result α)))

/-- Postconditions on successful returns hold vacuously at the bottom. -/
theorem admissible_success (post : α → Prop) :
    admissible (fun computation : Result α => ∀ value, computation = .ok value → post value) := by
  apply admissible_flatOrder
  change ∀ value, (Result.error .exhausted : Result α) = .ok value → post value
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
  · rename_i exception
    cases exception
    case exhausted => exact PartialOrder.rel_refl
    all_goals simpa using errors _

theorem bind_eq_ok (computation : Result α) (next : α → Result β) (value : β) :
    (computation >>= next) = .ok value ↔
      ∃ input, computation = .ok input ∧ next input = .ok value := by
  cases computation <;> simp

end Lynx.Result

namespace Lynx.Except
open Lean.Order

/-! Pure computations approximate a result by not returning, or return it
exactly. Handlers propagate `exhausted`, so every combinator is monotone and
`partial_fixpoint` proves monotonicity of translated bodies itself. -/

instance instPartialOrder : PartialOrder (Except Exception α) :=
  inferInstanceAs (PartialOrder (FlatOrder (.error .exhausted : Except Exception α)))

noncomputable instance instCCPO : CCPO (Except Exception α) :=
  inferInstanceAs (CCPO (FlatOrder (.error .exhausted : Except Exception α)))

instance : MonoBind (Except Exception) where
  bind_mono_left below := by
    change FlatOrder.rel _ _ at below
    cases below
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right := by
    intro _ _ computation _ _ below
    cases computation
    · exact FlatOrder.rel.refl
    · exact below _

/-- Fixed-point induction can establish any property that holds when the
computation does not return. -/
theorem admissible_of_bottom (property : Except Exception α → Prop)
    (bottom : property (.error .exhausted)) : admissible property :=
  admissible_flatOrder (b := (.error .exhausted : Except Exception α)) property bottom

/-- Postconditions on successful returns hold vacuously at the bottom. -/
theorem admissible_success (post : α → Prop) :
    admissible (fun computation : Except Exception α =>
      ∀ value, computation = .ok value → post value) :=
  admissible_of_bottom _ (by simp)

/-- A computation below another either does not return or equals it. -/
private theorem rel_cases {left right : Except Exception α} (below : left ⊑ right) :
    left = .error .exhausted ∨ left = right := by
  change FlatOrder.rel _ _ at below
  cases below
  · exact .inl rfl
  · exact .inr rfl

private theorem bot_rel (computation : Except Exception α) :
    (.error .exhausted : Except Exception α) ⊑ computation := FlatOrder.rel.bot

@[partial_fixpoint_monotone] theorem monotone_tryWith [PartialOrder γ]
    (computation : γ → Except Exception α) (next : γ → α → Except Exception β)
    (handler : γ → Exception → Except Exception β)
    (computationMono : monotone computation) (nextMono : monotone next)
    (handlerMono : monotone handler) :
    monotone fun x => tryWith (computation x) (next x) (handler x) := by
  intro x y below
  dsimp only
  rcases rel_cases (computationMono x y below) with bottom | same
  · rw [bottom]; exact bot_rel _
  · rw [← same]
    cases computation x with
    | ok value => exact nextMono x y below value
    | error exception =>
      cases exception
      case exhausted => exact PartialOrder.rel_refl
      all_goals exact handlerMono x y below _

@[partial_fixpoint_monotone] theorem monotone_guard [PartialOrder γ]
    (computation : γ → Except Exception Term) (body next : γ → Unit → Except Exception α)
    (computationMono : monotone computation) (bodyMono : monotone body)
    (nextMono : monotone next) :
    monotone fun x => guard (computation x) (body x) (next x) := by
  apply monotone_tryWith _ _ _ computationMono
  · intro x y below value
    dsimp only
    split
    · exact bodyMono x y below ()
    · exact nextMono x y below ()
  · intro x y below _
    exact nextMono x y below ()

@[partial_fixpoint_monotone] theorem monotone_orElse [PartialOrder γ]
    (left right : γ → Except Exception Term) (leftMono : monotone left)
    (rightMono : monotone right) :
    monotone fun x => orElse (left x) (right x) := by
  apply monotone_bind (Except Exception) _ _ leftMono
  intro x y below value
  dsimp only
  split
  · exact PartialOrder.rel_refl
  · exact rightMono x y below
  · exact PartialOrder.rel_refl

@[partial_fixpoint_monotone] theorem monotone_andAlso [PartialOrder γ]
    (left right : γ → Except Exception Term) (leftMono : monotone left)
    (rightMono : monotone right) :
    monotone fun x => andAlso (left x) (right x) := by
  apply monotone_bind (Except Exception) _ _ leftMono
  intro x y below value
  dsimp only
  split
  · exact rightMono x y below
  · exact PartialOrder.rel_refl
  · exact PartialOrder.rel_refl

end Lynx.Except
