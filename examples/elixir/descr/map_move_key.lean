namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-- A map of values with the value of one key moved to another, and the first key absent. -/
def mvK (a c : String) (w : MW V) : MW V :=
  fun k => if k = .atom a then none else if k = .atom c then w (.atom a) else w k

theorem mvK_in {a c : String} (ne : a ≠ c) {tag : Term} {l : List (Term × Term)} (ha : mapLookup l (.atom a) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} (h : MSem den tag l w) : MSem den tag l (mvK a c w) := by
  refine ⟨fun s => ?_, fun k i => by simpa [mvK] using h.doms k i⟩
  by_cases hs : s = a
  · subst hs; unfold FSem; rw [ha]; simp [mvK, tagSem_none]
  · by_cases hs' : s = c
    · subst hs'
      have := h.atoms a
      unfold FSem at this ⊢
      rw [ha] at this; rw [hc]
      simpa [mvK, Ne.symm ne] using this
    · simpa [mvK, hs, hs'] using h.atoms s

theorem mvK_back {a c : String} (ne : a ≠ c) {tag : Term} {l : List (Term × Term)} (ha : mapLookup l (.atom a) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} (h : MSem den tag l (mvK a c w))
    (tc : TagSem den tag "atom" (w (.atom c))) : MSem den tag l w := by
  refine ⟨fun s => ?_, fun k i => by simpa [mvK] using h.doms k i⟩
  by_cases hs : s = a
  · subst hs
    have := h.atoms c
    unfold FSem at this ⊢
    rw [hc] at this; rw [ha]
    simpa [mvK, Ne.symm ne] using this
  · by_cases hs' : s = c
    · subst hs'; unfold FSem; rw [hc]; exact tc
    · simpa [mvK, hs, hs'] using h.atoms s

/-- Keys of fields. -/
def keyStrs (l : List (Term × Term)) : List String := l.filterMap fun e => match e.1 with
  | .atom s => some s
  | _ => none

theorem lookup_fresh' {l : List (Term × Term)} {c : String} (h : c ∉ keyStrs l) : mapLookup l (.atom c) = none :=
  lookup_none fun e me eq => h (List.mem_filterMap.mpr ⟨e, me, by rw [eq]⟩)

/-- Strings longer than a bound, of distinct lengths. -/
def freshStrs (M n : Nat) : List String := (List.range n).map fun k => String.ofList (List.replicate (M + k + 1) 'x')

theorem freshStrs_len {M n : Nat} {c : String} (h : c ∈ freshStrs M n) : M < c.length := by
  simp only [freshStrs, List.mem_map, List.mem_range] at h
  obtain ⟨k, -, rfl⟩ := h
  simp; omega

theorem freshStrs_nodup (M n : Nat) : (freshStrs M n).Nodup := by
  unfold freshStrs List.Nodup
  rw [List.pairwise_map]
  refine (List.nodup_range).imp fun {x y} h e => h ?_
  have := congrArg String.length e
  simp at this; omega

theorem freshStrs_length (M n : Nat) : (freshStrs M n).length = n := by simp [freshStrs]

/-- Literals that do not hold maps whose key has been moved to a fresh key, for one of a list of fresh keys. -/
theorem survive (a : String) {w : MW V} (Ns : List (Term × List (Term × Term)))
    (hN : ∀ N ∈ Ns, mapLookup N.2 (.atom a) = none) (out : ∀ N ∈ Ns, ¬MSem den N.1 N.2 w) :
    ∀ (C : List String), C.Nodup → (∀ c ∈ C, c ≠ a ∧ ∀ N ∈ Ns, mapLookup N.2 (.atom c) = none) →
      Ns.length < C.length → ∃ c ∈ C, ∀ N ∈ Ns, ¬MSem den N.1 N.2 (mvK a c w) := by
  induction Ns with
  | nil =>
    intro C _ _ len
    cases C with
    | nil => simp at len
    | cons c _ => exact ⟨c, List.mem_cons_self, by simp⟩
  | cons N rest ih =>
    intro C nd fr len
    have hN' := fun N' (m : N' ∈ rest) => hN N' (List.mem_cons_of_mem _ m)
    have out' := fun N' (m : N' ∈ rest) => out N' (List.mem_cons_of_mem _ m)
    have fr' : ∀ c ∈ C, c ≠ a ∧ ∀ N' ∈ rest, mapLookup N'.2 (.atom c) = none :=
      fun c mc => ⟨(fr c mc).1, fun N' m => (fr c mc).2 N' (List.mem_cons_of_mem _ m)⟩
    by_cases killed : ∃ c₀ ∈ C, MSem den N.1 N.2 (mvK a c₀ w)
    · obtain ⟨c₀, mc₀, h₀⟩ := killed
      -- Only that key: another one would show the literal holds the map itself.
      have only : ∀ c ∈ C, c ≠ c₀ → ¬MSem den N.1 N.2 (mvK a c w) := by
        intro c mc ne hc
        have na₀ := (fr c₀ mc₀).1
        have hc₀ := (fr c₀ mc₀).2 N List.mem_cons_self
        have tc : TagSem den N.1 "atom" (w (.atom c₀)) := by
          have := hc.atoms c₀
          unfold FSem at this
          rw [hc₀] at this
          simpa [mvK, na₀, Ne.symm ne] using this
        exact out N List.mem_cons_self
          (mvK_back (Ne.symm na₀) (hN N List.mem_cons_self) hc₀ h₀ tc)
      obtain ⟨c, mc, hc⟩ := ih hN' out' (C.erase c₀) (nd.erase c₀)
        (fun c m => fr' c (List.mem_of_mem_erase m)) (by rw [List.length_erase_of_mem mc₀]; simp at len; omega)
      have ne : c ≠ c₀ := fun e => by subst e; exact (List.Nodup.not_mem_erase nd) mc
      refine ⟨c, List.mem_of_mem_erase mc, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact only c (List.mem_of_mem_erase mc) ne
      · exact hc N' m
    · obtain ⟨c, mc, hc⟩ := ih hN' out' C nd fr' (by simp at len; omega)
      refine ⟨c, mc, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact fun h => killed ⟨c, mc, h⟩
      · exact hc N' m

theorem le_maxLen : ∀ (L : List String), ∀ s ∈ L, s.length ≤ (L.map String.length).foldr max 0
  | [], _, h => by simp at h
  | x :: L, s, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxLen L s h) (Nat.le_max_right _ _)

/-- A map in a literal and outside others, none of which mention a key, can do without the key. -/
theorem aless (a : String) {tag : Term} {l : List (Term × Term)} (hB : mapLookup l (.atom a) = none)
    (Ns : List (Term × List (Term × Term))) (hN : ∀ N ∈ Ns, mapLookup N.2 (.atom a) = none) {w : MW V}
    (hb : MSem den tag l w) (out : ∀ N ∈ Ns, ¬MSem den N.1 N.2 w) :
    ∃ u : MW V, u (.atom a) = none ∧ MSem den tag l u ∧ ∀ N ∈ Ns, ¬MSem den N.1 N.2 u := by
  let L : List String := a :: keyStrs l ++ Ns.flatMap fun N => keyStrs N.2
  let M := (L.map String.length).foldr max 0
  have fresh : ∀ c ∈ freshStrs M (Ns.length + 1), c ∉ L := fun c mc mL => by
    have := le_maxLen L c mL; have := freshStrs_len mc; omega
  obtain ⟨c, mc, hc⟩ := survive a Ns hN out (freshStrs M (Ns.length + 1)) (freshStrs_nodup M _)
    (fun c mc => ⟨fun e => fresh c mc (by simp [L, e]), fun N mN => lookup_fresh' fun m =>
      fresh c mc (by simp only [L, List.mem_cons, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨N, mN, m⟩)⟩)
    (by rw [freshStrs_length]; omega)
  have na : a ≠ c := fun e => fresh c mc (by simp [L, e])
  refine ⟨mvK a c w, by simp [mvK], mvK_in na hB (lookup_fresh' fun m => fresh c mc (by simp [L, m])) hb, hc⟩

end

end Elixir.STTDescrProofsTest.Nest
