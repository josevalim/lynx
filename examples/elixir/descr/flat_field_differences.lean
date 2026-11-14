namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences of fields of flat types, on points of values. -/

/-- Differences of function types hold the arities of the first and not the second. -/
theorem fun_diff_spec (n : Nat) {x y : Term} (fx : FunF x) (fy : FunF y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun") x y = .ok w ∧
      (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = (arityOf x a ρ && !arityOf y a ρ)) ∧
      (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → (arityOf x a ρ && !arityOf y a ρ) = Bool.false) := by
  have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
    intro M ne; cases M with
    | nil => exact absurd rfl ne
    | cons e rest => exact size_cons e rest
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  cases p₁ <;> cases p₂
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 2) b₂ b₁
    exact fun_finish Bool.true M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => by
        subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»])
      (fun _ hM => by
        obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne])
  · obtain ⟨M, run, bM, sem, -⟩ := repr_union_sem (n + 1) b₁ b₂
    exact fun_finish Bool.false M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]
        cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun _ => by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso])
      (fun h => by cases h) (fun h => by cases h)
  · obtain ⟨M, run, bM, sem, -⟩ := repr_inter_sem (n + 1) b₁ b₂
    exact fun_finish Bool.true M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]
        cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => by
        subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»])
      (fun _ hM => by
        obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne])
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 2) b₁ b₂
    exact fun_finish Bool.true M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => by
        subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»])
      (fun _ hM => by
        obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne])

end Elixir.STTDescrProofsTest
