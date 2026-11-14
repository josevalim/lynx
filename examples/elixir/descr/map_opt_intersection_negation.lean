namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of map negations on value maps. -/

theorem closed_lt_openM {k H : Int} (hk : k < 0) (hH : 0 ≤ H) (cl fo : Term) :
    Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer H, .atom "open", fo])) (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer H, .atom "open", fo]) = .lt := by
  rw [compare_tuple]
  have : Ord.compare k H = .lt := Int.compare_eq_lt.mpr (by omega)
  simp [List.compareLex_cons_cons, this]

end Elixir.STTDescrProofsTest
