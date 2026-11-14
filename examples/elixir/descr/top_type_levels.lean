namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The top type is a top-level type at every level, and the laws use the level of their depth. -/

section
variable {L : Level} {m : Nat}

theorem tc_term : TC L (.atom "term") := Or.inl rfl

end

theorem level_K (t : Term) : ∀ n, (level t n).K = 23 + 24 * n
  | 0 => rfl
  | n + 1 => by
    show (level t n).K + 24 = _
    rw [level_K t n]
    omega

end Elixir.STTDescrProofsTest.Nest
