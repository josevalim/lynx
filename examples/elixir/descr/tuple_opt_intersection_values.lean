namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of tuple types on tuples of values. -/

/-- The intersection function of optimized tuple leaf intersections. -/
def optTupleIFun (S : Term) : Term :=
  .function "Elixir.Module.Types.Descr" "-opt_tuple_leaf_intersection/3-fun-0-" 2 #[S]

theorem closed_lt_open' {k H : Int} (hk : k < 0) (hH : 0 ≤ H) (cl fo : Term) :
    Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer H, .atom "open", fo])) (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer H, .atom "open", fo]) = .lt := by
  rw [compare_tuple]
  have : Ord.compare k H = .lt := Int.compare_eq_lt.mpr (by omega)
  simp [List.compareLex_cons_cons, this]

theorem tupleLit_elems {E : Term → Prop} {k : Int} {t : String} {l : List Term}
    (h : TupleLit E (.tuple #[.integer k, .atom t, Term.list l])) : ∀ e ∈ l, E e := by
  obtain ⟨k', t', l', e, -, hl⟩ := h
  simp only [Term.tuple.injEq] at e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₂
  rw [list_inj e₂]
  exact hl

end Elixir.STTDescrProofsTest
