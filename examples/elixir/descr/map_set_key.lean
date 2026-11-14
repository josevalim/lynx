namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-- A map of values with one key set. -/
def setW (κ : MKey) (o : Option V) (w : MW V) : MW V := fun k => if k = κ then o else w k

/-- A literal holding a map with either of two keys set holds the map itself. -/
theorem msem_two {tag : Term} {l : List (Term × Term)} {w : MW V} {κ₁ κ₂ : MKey} (ne : κ₁ ≠ κ₂) {o : Option V}
    (h₁ : MSem den tag l (setW κ₁ o w)) (h₂ : MSem den tag l (setW κ₂ o w)) : MSem den tag l w := by
  rw [msem_keys] at h₁ h₂ ⊢
  intro κ
  by_cases e : κ = κ₁
  · subst e; simpa [setW, ne] using h₂ κ
  · simpa [setW, e] using h₁ κ

theorem nsem_two {N : Term} {w : MW V} {κ₁ κ₂ : MKey} (ne : κ₁ ≠ κ₂) {o : Option V}
    (h₁ : NSem den N (setW κ₁ o w)) (h₂ : NSem den N (setW κ₂ o w)) : NSem den N w := by
  obtain ⟨k, tag, l, rfl, m₁⟩ := h₁
  obtain ⟨k', tag', l', e, m₂⟩ := h₂
  obtain ⟨-, rfl, e₃⟩ := tuple3_inj e
  rw [← fieldsTerm_inj e₃] at m₂
  exact ⟨k, tag, l, rfl, msem_two ne m₁ m₂⟩

/-- Negated literals miss a map with one of many keys set, when they miss the map. -/
theorem survive_set {w : MW V} (o : Option V) : ∀ (Ns : List Term), (∀ N ∈ Ns, ¬NSem den N w) →
    ∀ (C : List MKey), C.Nodup → Ns.length < C.length → ∃ κ ∈ C, ∀ N ∈ Ns, ¬NSem den N (setW κ o w) := by
  intro Ns
  induction Ns with
  | nil =>
    intro _ C _ len
    cases C with
    | nil => simp at len
    | cons κ _ => exact ⟨κ, List.mem_cons_self, by simp⟩
  | cons N rest ih =>
    intro out C nd len
    have out' := fun N' (m : N' ∈ rest) => out N' (List.mem_cons_of_mem _ m)
    by_cases killed : ∃ κ₀ ∈ C, NSem den N (setW κ₀ o w)
    · obtain ⟨κ₀, mκ₀, h₀⟩ := killed
      obtain ⟨κ, mκ, hκ⟩ := ih out' (C.erase κ₀) (nd.erase κ₀) (by rw [List.length_erase_of_mem mκ₀]; simp at len; omega)
      have ne : κ ≠ κ₀ := fun e => by subst e; exact (List.Nodup.not_mem_erase nd) mκ
      refine ⟨κ, List.mem_of_mem_erase mκ, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact fun h => out N' List.mem_cons_self (nsem_two ne h h₀)
      · exact hκ N' m
    · obtain ⟨κ, mκ, hκ⟩ := ih out' C nd (by simp at len; omega)
      refine ⟨κ, mκ, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact fun h => killed ⟨κ, mκ, h⟩
      · exact hκ N' m

/-- Values a literal allows at one of many keys occur at one of them in a map of a non-empty line. -/
theorem line_witness {tag : Term} {l : List (Term × Term)} {negs : List Term} {w₀ : MW V}
    (h₀ : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w₀) {x : V} (C : List MKey) (nd : C.Nodup)
    (len : negs.length < C.length) (hC : ∀ κ ∈ C, KeyAllow den tag l κ (some x)) :
    ∃ κ ∈ C, ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w ∧ w κ = some x := by
  obtain ⟨hm, hn⟩ := inMLine_iff.mp h₀
  obtain ⟨κ, mκ, out⟩ := survive_set (some x) negs hn C nd len
  refine ⟨κ, mκ, setW κ (some x) w₀, inMLine_iff.mpr ⟨msem_keys.mpr fun κ' => ?_, out⟩, by simp [setW]⟩
  by_cases e : κ' = κ
  · subst e; simpa [setW] using hC κ' mκ
  · simpa [setW, e] using msem_keys.mp hm κ'

/-- A map of values with two atom keys swapped. -/
def swapW (s c : String) (w : MW V) : MW V :=
  fun k => if k = .atom s then w (.atom c) else if k = .atom c then w (.atom s) else w k

theorem swapW_swapW (s c : String) (w : MW V) : swapW s c (swapW s c w) = w := by
  funext k
  by_cases hs : k = .atom s
  · subst hs; by_cases e : s = c
    · subst e; simp [swapW]
    · simp [swapW, Ne.symm e]
  · by_cases hc : k = .atom c
    · subst hc; simp [swapW, hs]
    · simp [swapW, hs, hc]

/-- Literals that mention neither of two atom keys hold maps with the keys swapped. -/
theorem msem_swapW {s c : String} {tag : Term} {l : List (Term × Term)} (hs : mapLookup l (.atom s) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} (h : MSem den tag l w) : MSem den tag l (swapW s c w) := by
  refine ⟨fun a => ?_, fun k i => by simpa [swapW] using h.doms k i⟩
  by_cases ha : a = s
  · subst ha
    have := h.atoms c
    unfold FSem at this ⊢
    rw [hc] at this; rw [hs]
    simpa [swapW] using this
  · by_cases hc' : a = c
    · subst hc'
      have := h.atoms s
      unfold FSem at this ⊢
      rw [hs] at this; rw [hc]
      simpa [swapW, ha] using this
    · simpa [swapW, ha, hc'] using h.atoms a

theorem msem_swapW_iff {s c : String} {tag : Term} {l : List (Term × Term)} (hs : mapLookup l (.atom s) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} : MSem den tag l (swapW s c w) ↔ MSem den tag l w :=
  ⟨fun h => by simpa [swapW_swapW] using msem_swapW hs hc h, msem_swapW hs hc⟩

theorem fresh_str (L : List String) : ∃ c, c ∉ L := by
  obtain ⟨c, mc⟩ : ∃ c, c ∈ freshStrs ((L.map String.length).foldr max 0) 1 := ⟨_, by simp [freshStrs]; rfl⟩
  exact ⟨c, fun m => by have := le_maxLen L c m; have := freshStrs_len mc; omega⟩

end

end Elixir.STTDescrProofsTest.Nest
