namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of basic types. -/

theorem opt_inter_key (depth : Nat) (name : String) (x y S : Term) (hx : FieldOk name x) (hy : FieldOk name y) :
    ∃ r, Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) (.atom name) x y S = .ok r ∧
      (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
      (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a &&& b)) ∧
      (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
        (amemV (some x) q && amemV (some y) q)) ∧
      (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.true) := by
  by_cases bf : name = "bitmap" ∨ name = "atom" ∨ name = "fun"
  · obtain ⟨r, run, rest⟩ := inter_key name x y hx hy
    refine ⟨r, ?_, rest⟩
    rw [opt_inter4_eq depth (by rcases bf with rfl | rfl | rfl <;> simp) S]
    exact run _
  · have nb : name ≠ "bitmap" := fun e => bf (Or.inl e)
    have na : name ≠ "atom" := fun e => bf (Or.inr (Or.inl e))
    have nf : name ≠ "fun" := fun e => bf (Or.inr (Or.inr e))
    have tx : topValue name = some x := by
      rcases hx with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, t⟩
      · exact absurd e nb
      · exact absurd e na
      · exact t
    have ty : topValue name = some y := by
      rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, t⟩
      · exact absurd e nb
      · exact absurd e na
      · exact t
    have xy : x = y := by rw [tx] at ty; cases ty; rfl
    subst xy
    have names : name = "list" ∨ name = "tuple" ∨ name = "map" := by
      unfold topValue at tx
      split at tx <;> simp_all
    refine ⟨x, ?_, fun _ => hx, fun e => absurd e nb, fun e => absurd e na, fun _ _ => ?_⟩
    · rcases names with rfl | rfl | rfl <;> simp only [topValue, Option.some.injEq] at tx <;> subst tx <;> rfl
    · rcases names with rfl | rfl | rfl <;> simp [topValue] at tx <;> subst tx <;> simp [kept]

theorem opt_inter_term_l (d : Dispatcher) (x S : Term) :
    Elixir.Module.Types.Descr.«opt_intersection/3» d (.atom "term") x S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/3»; rfl

/-- The intersection function of optimized map leaf intersections. -/
def optMapIFun (S : Term) : Term := .function "Elixir.Module.Types.Descr" "-opt_map_leaf_intersection/3-fun-0-" 2 #[S]

end Elixir.STTDescrProofsTest
