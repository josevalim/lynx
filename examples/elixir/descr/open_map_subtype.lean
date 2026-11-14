namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem eq_nil_of_compare {a : Term} (h : Term.compare (Term.fuel a .nil) a .nil = .eq) : a = .nil := by
  cases a <;> rw [Term.compare_step] at h <;> simp [Compare.compareStep] at h ⊢

theorem nil_of_eq {a : Term} (h : Erlang.erlang.«==/2» a .nil = .ok (.atom "true")) : a = .nil := by
  simp only [Erlang.erlang.«==/2»] at h
  split at h
  · exact eq_nil_of_compare ‹_›
  · simp at h

theorem atom_list_ok : ∀ (A : Term), Elixir.STTDescrProofsTest.«atom_list?/1» A = .ok (.atom "true") →
    ∃ as, A = Term.list as ∧ ∀ a ∈ as, ∃ s, a = .atom s
  | .cons a rest, h => by
    rw [Elixir.STTDescrProofsTest.«atom_list?/1».eq_def] at h
    simp only [Lynx.Except.andAlso_eq_true] at h
    obtain ⟨as, rfl, has⟩ := atom_list_ok rest h.2
    obtain ⟨s, rfl⟩ : ∃ s, a = .atom s := by
      cases a <;> simp [Erlang.erlang.«is_atom/1»] at h
      exact ⟨_, rfl⟩
    exact ⟨.atom s :: as, rfl, fun b mb => (List.mem_cons.mp mb).elim (fun e => ⟨s, e⟩) (has b)⟩
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .integer _, h | .float _, h | .atom _, h | .reference _, h | .function _ _ _ _, h | .pid _, h | .tuple _, h
  | .map _, h | .bitstring _ _ _, h => by
    rw [Elixir.STTDescrProofsTest.«atom_list?/1».eq_def] at h
    cases nil_of_eq h

theorem isMember_true {v : Term} : ∀ {L : List Term}, isMember v L = .atom "true" → ∃ c ∈ L, compareExact (fuel v c) v c = .eq
  | [], h => by simp at h
  | c :: rest, h => by
    simp only [isMember] at h
    split at h
    · exact ⟨c, List.mem_cons_self, ‹_›⟩
    · obtain ⟨c', m', e'⟩ := isMember_true h
      exact ⟨c', List.mem_cons_of_mem _ m', e'⟩

theorem domain_kind_ok {a : Term} (h : Elixir.STTDescrProofsTest.«domain_kind?/1» a = .ok (.atom "true")) :
    ∃ s ∈ domainKinds, a = .atom s := by
  simp only [Elixir.STTDescrProofsTest.«domain_kind?/1», Lynx.Except.guard, Lynx.Except.tryWith] at h
  generalize hm : isMember a _ = r at h
  by_cases e : r = .atom "true"
  · subst e
    obtain ⟨c, mc, ec⟩ := isMember_true hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mc
    rcases mc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, by simp [domainKinds], (compareExact_eq_atom _ _).mp ec⟩
  · clear hm
    split at h
    · exact absurd rfl e
    · simp at h

theorem kind_list_ok : ∀ (A : Term), Elixir.STTDescrProofsTest.«kind_list?/1» A = .ok (.atom "true") →
    ∃ ks, A = Term.list ks ∧ ∀ d ∈ ks, ∃ s ∈ domainKinds, d = .atom s
  | .cons a rest, h => by
    rw [Elixir.STTDescrProofsTest.«kind_list?/1».eq_def] at h
    simp only [Lynx.Except.andAlso_eq_true] at h
    obtain ⟨ks, rfl, hks⟩ := kind_list_ok rest h.2
    obtain ⟨s, ms, rfl⟩ : ∃ s ∈ domainKinds, a = .atom s := by
      exact domain_kind_ok h.1
    exact ⟨.atom s :: ks, rfl, fun b mb => (List.mem_cons.mp mb).elim (fun e => ⟨s, ms, e⟩) (hks b)⟩
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .integer _, h | .float _, h | .atom _, h | .reference _, h | .function _ _ _ _, h | .pid _, h | .tuple _, h
  | .map _, h | .bitstring _ _ _, h => by
    rw [Elixir.STTDescrProofsTest.«kind_list?/1».eq_def] at h
    cases nil_of_eq h

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem keys_ok {A K : Term} (h : Elixir.STTDescrProofsTest.«keys?/2» A K = .ok (.atom "true")) :
    ∃ as ks, A = Term.list as ∧ K = Term.list ks ∧ (∀ a ∈ as, ∃ s, a = .atom s) ∧
      ∀ d ∈ ks, ∃ s ∈ domainKinds, d = .atom s := by
  simp only [Elixir.STTDescrProofsTest.«keys?/2», Lynx.Except.andAlso_eq_true] at h
  obtain ⟨as, rfl, ha⟩ := atom_list_ok _ h.1
  obtain ⟨ks, rfl, hk⟩ := kind_list_ok _ h.2
  exact ⟨as, ks, rfl, rfl, ha, hk⟩

/-- Types holding only maps, with some map, are subtypes of `open_map()` holding some point. -/
theorem monly_iff {t : Term} {n : Nat} {X : List (Term × Term)} :
    MOnly t n X ↔ SubN t n (.map X) (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) ∧
      ¬∀ v : PN t n, ¬denD (.map X) v := by
  constructor
  · rintro ⟨h₁, w, hw⟩
    exact ⟨fun v hv => (mapTop_den v).mpr (h₁ v hv), fun h => h _ ((denD_mpt w).mpr hw)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun v hv => (mapTop_den v).mp (h₁ v hv), ?_⟩
    obtain ⟨v, hv⟩ := Classical.not_forall.mp h₂
    have hv := Classical.not_not.mp hv
    obtain ⟨w, hw⟩ := pt_map v ((mapTop_den v).mp (h₁ v hv))
    exact ⟨w, (hw X).mp hv⟩

end Elixir.STTDescrProofsTest.Nest
