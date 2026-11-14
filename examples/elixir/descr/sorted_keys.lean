namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

theorem lt_true {a b : Term} (h : Erlang.erlang.«</2» a b = .ok Term.true) : Term.compare (Term.fuel a b) a b = .lt := by
  refine Classical.byContradiction fun ne => ?_
  simp [Erlang.erlang.«</2», ne, Term.true] at h

theorem is_atom_true {a : Term} (h : Erlang.erlang.«is_atom/1» a = .ok Term.true) : ∃ s : String, a = .atom s := by
  cases a <;> simp_all [Erlang.erlang.«is_atom/1», Term.true]

/-- The keys `sorted_keys?/1` checks: atoms in increasing order. -/
theorem sorted_keys_spec : ∀ l : List (Term × Term), «sorted_keys?/1» (fieldsTerm l) = .ok Term.true →
    (∀ e ∈ l, ∃ s : String, e.1 = .atom s) ∧ l.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)
  | [], _ => ⟨by simp, by simp⟩
  | [(k, v)], h => by
    rw [«sorted_keys?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    exact ⟨by simpa using is_atom_true h, by simp⟩
  | (k, v) :: (k', v') :: rest, h => by
    rw [«sorted_keys?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨ha, hlt⟩, hr⟩ := h
    obtain ⟨keys, pw⟩ := sorted_keys_spec ((k', v') :: rest) (by simpa [fieldsTerm, Term.list] using hr)
    have lt := lt_true (by simpa [Term.true] using hlt)
    refine ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨fun e me => ?_, pw⟩⟩
    · rcases List.mem_cons.mp me with rfl | me
      · exact is_atom_true (by simpa [Term.true] using ha)
      · exact keys e me
    · rcases List.mem_cons.mp me with rfl | me
      · exact lt
      · exact cmp_lt_trans lt ((List.pairwise_cons.mp pw).1 e me)

end Elixir.STTDescrProofsTest
