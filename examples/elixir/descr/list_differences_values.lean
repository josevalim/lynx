namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences of list types on lists of values. -/

abbrev optListCmp : Term := .function "Elixir.Module.Types.Descr" "opt_list_leaf_difference" 3 #[]

/-- The clause of `opt_list_difference/3` for two list literals. -/
theorem opt_list_leaves {d : Dispatcher} {S k₁ l₁ t₁ k₂ l₂ t₂ : Term}
    (nt : ¬(l₁ = .atom "term" ∧ t₁ = .atom "term"))
    (ne : compareExact (fuel (.tuple #[k₂, l₂, t₂]) (.tuple #[k₁, l₁, t₁])) (.tuple #[k₂, l₂, t₂]) (.tuple #[k₁, l₁, t₁]) ≠ .eq) :
    (Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        Elixir.Module.Types.Descr.«bdd_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) optListCmp) ∧
    (Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«subtype?/2» d t₁ t₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        .ok (.atom "bdd_bot")) ∧
    (Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«subtype?/2» d t₁ t₂ = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_difference") (.tuple #[k₁, l₁, t₁])
        (.tuple #[k₂, l₂, t₂]) = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂])) ∧
    (∀ S', Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«subtype?/2» d t₁ t₂ = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_difference") (.tuple #[k₁, l₁, t₁])
        (.tuple #[k₂, l₂, t₂]) = .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        (Elixir.Module.Types.Descr.«opt_difference/3» d t₁ t₂ S' >>=
          fun c => Elixir.Module.Types.Descr.«bdd_leaf_new/2» l₁ c)) := by
  refine ⟨fun h₁ => ?_, fun h₁ h₂ => ?_, fun h₁ h₂ h₃ => ?_, fun S' h₁ h₂ h₃ => ?_⟩ <;>
  · rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
    simp only [leaf_guard]
    rw [ite_eq_right (by simpa using ne)]
    split
    · exfalso; simp_all
    · rename_i heq₁ heq₂
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_eq heq₁
      obtain ⟨e₄, e₅, e₆⟩ := tuple3_eq heq₂
      subst e₁ e₂ e₃ e₄ e₅ e₆
      simp [*, Lynx.Except.andAlso, Erlang.erlang.«/=/2», optListCmp]
    · next h => exact (h _ _ _ _ _ _ rfl rfl).elim

theorem opt_list_same {d : Dispatcher} {S k a b y : Term} (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k, a, b]) y S = .ok (.atom "bdd_bot") := by
  rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
  simp only [leaf_guard]
  rw [ite_eq_left (by simpa using e)]
  rfl

/-- The top list leaf less a list field: the empty BDD when they are exactly equal, its negation otherwise. -/
theorem opt_list_top {d : Dispatcher} {S k y : Term} :
    Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k, .atom "term", .atom "term"]) y S =
      if compareExact (fuel y (.tuple #[k, .atom "term", .atom "term"])) y (.tuple #[k, .atom "term", .atom "term"]) = .eq then .ok (.atom "bdd_bot")
      else Elixir.Module.Types.Descr.«bdd_negation/1» y := by
  rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
  simp only [leaf_guard]
  split <;> simp_all

theorem opt_list_other {d : Dispatcher} {S x y : Term} (nt : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"])
    (nl : ¬((∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b])) :
    Elixir.Module.Types.Descr.«opt_list_difference/3» d x y S =
      Elixir.Module.Types.Descr.«bdd_difference/3» d x y optListCmp := by
  rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
  simp only [leaf_guard]
  split
  · rw [ite_eq_right]
    · split
      · exfalso; simp_all
      · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
      · rfl
    · intro e
      obtain ⟨a, b, c, rfl, -⟩ := exact_tuple3 e
      exact nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩
  · split
    · exact (nt _ rfl).elim
    · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
    · rfl

end Elixir.STTDescrProofsTest
