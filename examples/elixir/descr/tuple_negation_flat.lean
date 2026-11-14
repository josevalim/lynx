namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Negations of tuple types of flat element types. -/

theorem opt_bdd_seen_map (S : List (Term × Term)) (op a b : Term) :
    Elixir.Module.Types.Descr.«opt_bdd_seen/4» (.map S) op a b = .ok (.atom "seen") ∨
      ∃ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» (.map S) op a b = .ok (.tuple #[.atom "ok", .map S']) := by
  unfold Elixir.Module.Types.Descr.«opt_bdd_seen/4»
  cases h : mapLookup S (.tuple #[op, a, b]) with
  | none => exact Or.inr ⟨(.tuple #[op, a, b], .atom "true") :: S, by simp [getMapKeys_single, h, Erlang.maps.«put/3»]⟩
  | some w => exact Or.inl (by simp [getMapKeys_single, h])

end Elixir.STTDescrProofsTest
