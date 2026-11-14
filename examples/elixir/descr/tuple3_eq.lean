namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of map types on value maps. -/

theorem tuple3_eq {a b c a' b' c' : Term} (h : Term.tuple #[a, b, c] = .tuple #[a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun x : Array Term => x[0]?) h
  have e₁ := congrArg (fun x : Array Term => x[1]?) h
  have e₂ := congrArg (fun x : Array Term => x[2]?) h
  simp at e₀ e₁ e₂
  exact ⟨e₀, e₁, e₂⟩

end Elixir.STTDescrProofsTest
