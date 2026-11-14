
namespace Elixir.STTDescrProofsTest.FunSem
variable {V : Type}

theorem args_set_empty : ∀ (args : List (Bool × (V → Prop))) (j : Nat) (e : V → Prop) (x : List (Option V)),
    j < args.length → (∀ v, ¬e v) → ¬Args (args.set j (true, e)) x
  | (b, a) :: as, 0, e, o :: os, _, he, h => by
    obtain ⟨ho, -⟩ := h
    cases o with
    | none => cases ho
    | some v => exact he v ho
  | (b, a) :: as, j + 1, e, o :: os, hj, he, h =>
    args_set_empty as j e os (by simp at hj; omega) he h.2
  | (b, a) :: as, j, e, [], _, _, h => by
    cases j <;> simp [List.set, Args] at h
  | [], _, _, _, hj, _, _ => by simp at hj

/-- `phi` holds when the return set is flagged and empty. -/
theorem phiS_empty_ret (args : List (Bool × (V → Prop))) (r : V → Prop) (P : List (Arrow V))
    (len : ∀ p ∈ P, p.1.length = args.length) (he : ∀ v, ¬r v) : phiS args (true, r) P := by
  rw [phiS_iff _ _ _ len]
  intro x y _ hy _
  cases y with
  | none => cases hy
  | some v => exact he v hy

/-- `phi` holds when an argument is flagged and empty. -/
theorem phiS_empty_arg (args : List (Bool × (V → Prop))) (j : Nat) (hj : j < args.length) (e : V → Prop)
    (ret : Bool × (V → Prop)) (P : List (Arrow V)) (len : ∀ p ∈ P, p.1.length = args.length) (he : ∀ v, ¬e v) :
    phiS (args.set j (true, e)) ret P := by
  rw [phiS_iff _ _ _ (by simpa using len)]
  intro x y hx
  exact absurd hx (args_set_empty args j e x hj he)

end Elixir.STTDescrProofsTest.FunSem

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

theorem encA_set (args : List (Bool × Term)) (j : Nat) (p : Bool × Term) :
    Term.list ((args.map fun p => Term.tuple #[boolAtom p.1, p.2]).set j (.tuple #[boolAtom p.1, p.2])) =
      encA (args.set j p) := by
  simp [encA, List.map_set]

theorem guard_member (b : Bool) {α : Type} (f g : Unit → Except Exception α) :
    Lynx.Except.guard (.ok ((boolAtom b).isMember [.atom "false", .atom "nil"])) f g = if b then g () else f () := by
  cases b <;> simp [boolAtom, Term.isMember]

end

end Elixir.STTDescrProofsTest.Nest
