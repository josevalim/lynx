namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of map literals on value maps. -/

/-- Optimized unions of element types are their unions. -/
theorem opt_union_top (n : Nat) {name : String} {w : Term} (hn : topValue name = some w) (S : Term) :
    Elixir.Module.Types.Descr.«opt_union/4» (D (n + 1)) (.atom name) w w S = .ok w := by
  rcases top_cases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [opt_union4_eq _ (Or.inr (Or.inr (Or.inl rfl)))]; exact fun_top_union n
  · rfl
  · have st := strategy_start (D (n + 1)) "open" "open" (Or.inl rfl) (Or.inl rfl) [] []
    simp only [Term.list, List.length_nil, and_self, ite_true] at st
    rw [show Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D (n + 1)) .nil .nil (.integer 0)
      (.atom "all_equal") = .ok (.atom "left_subtype_of_right") from index_nil_left _ [] _ _] at st
    simp only [Elixir.Module.Types.Descr.«opt_union/4»]
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2»]
  · rfl

theorem opt_diff_top (d : Dispatcher) {name : String} {w : Term} (hn : topValue name = some w) (S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/4» d (.atom name) w w S =
      Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) w w := by
  rcases top_cases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first
    | rfl
    | (simp only [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»]
       rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def, Elixir.Module.Types.Descr.«list_difference/2».eq_def]
       simp [Erlang.erlang.«=:=/2»])

end Elixir.STTDescrProofsTest
