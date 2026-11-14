namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized negations of map types on value maps. -/

theorem leaf_one_open (key f : Term) : ∃ H : Int, 0 ≤ H ∧
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.tuple #[key, f]]) =
      .ok (.tuple #[.integer H, .atom "open", fieldsTerm [(key, f)]]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.tuple #[key, f]]))
  refine ⟨(1 <<< 27) + hash, by omega, ?_⟩
  simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2»,
    Erlang.erlang.«is_list/1», Term.list, Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»,
    fieldsTerm]
  rfl

/-- Negations of maps other than the top map and open maps of one field are plain negations. -/
theorem opt_neg_plainK (k₀ : Int) (d : Dispatcher) (S : Term) {x : Term} (arr : Array Term) (hx : x = .tuple arr)
    (nt : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (none : ∀ k key f, x ≠ .tuple #[k, .atom "open", .cons (.tuple #[key, f]) .nil]) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d (.tuple #[.integer k₀, .atom "open", .nil]) x S = Elixir.Module.Types.Descr.«bdd_negation/1» x := by
  subst hx
  unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
  split
  · next heq => exact absurd heq (nt _)
  · simp only [leaf_guard]
    split
    · next e =>
      obtain ⟨a, b, c, e₀, -, e₂, e₃⟩ := exact_tuple3 e
      simp only [compareExact_eq_atom, compareExact_eq_nil] at e₂ e₃
      subst e₂ e₃
      exact absurd e₀ (nt a)
    · split
      · next heq => exact absurd heq (none _ _ _)
      · next heq => rw [heq]
      · next h => exact absurd rfl (h _ _ rfl)

end Elixir.STTDescrProofsTest
