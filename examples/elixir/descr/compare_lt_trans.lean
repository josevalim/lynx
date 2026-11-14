namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Completeness of map line emptiness on values. -/

theorem cmp_lt_trans {x y z : Term} (h₁ : Term.compare (Term.fuel x y) x y = .lt) (h₂ : Term.compare (Term.fuel y z) y z = .lt) :
    Term.compare (Term.fuel x z) x z = .lt := Lynx.Term.compare_lt_trans h₁ h₂

end Elixir.STTDescrProofsTest
