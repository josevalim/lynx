namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Unions of static map types of the next level are maps of the points of either. -/
theorem union_map {A B : List (Term × Term)} (hA : DE (level t n).E (.map A)) (hB : DE (level t n).E (.map B)) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B) = .ok (.map U) ∧
      DE (level t n).E (.map U) ∧ ∀ v : PN t n, denD (.map U) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  obtain ⟨c, hc, rc, sc, -⟩ := (ef_next t n).union hA hB
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have sA := de_map hA
  have sB := de_map hB
  obtain ⟨U, rU, -⟩ := union_any k A B sA.static sB.static (fun q h => let ⟨name, _, e⟩ := sB.keys q h; ⟨name, e⟩)
    (fun q x y hx hy => by
      obtain ⟨name, -, rfl⟩ := sA.keys q (by rw [hx]; rfl)
      obtain ⟨u, ru, -⟩ := fieldC_union (tks (level t n)) (tfc (level t n)) (m := k) (by omega)
        (sA.fields _ _ hx) (sB.fields _ _ hy)
      exact ⟨u, ru⟩)
  have e := (rc (k + 1) hm).symm.trans rU
  simp only [Except.ok.injEq] at e
  subst e
  exact ⟨U, rU, hc, sc⟩

theorem denD_single (name : String) (x : Term) (v : PN t n) :
    denD (.map [(.atom name, x)]) v ↔ v.1.1 = name ∧ dn name (some x) v.1.2 = Bool.true := by
  rw [denD_map, lookup_cons_atom]
  by_cases e : name = v.1.1
  · subst e; simp
  · simp [e, mapLookup, dn_none]
    exact fun h => absurd h.symm e

theorem single_de {name : String} {x : Term} (hn : name ∈ names)
    (fx : FieldC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) name x) :
    DE (level t n).E (.map [(.atom name, x)]) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name' w h => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
    by_cases e : compareExact (fuel q (.atom name)) q (.atom name) = .eq
    · exact ⟨name, hn, (compareExact_eq_atom _ _).mp e⟩
    · simp [e] at h
  · rw [lookup_cons_atom] at h
    by_cases e : name = name'
    · subst e; simp at h; subst h; exact fx
    · simp [e, mapLookup] at h

/-- Key types of a kind: their points are of that kind, every atom for the atom kind, and some point otherwise. -/
structure KindT (t : Term) (n : Nat) (d : String) (T : List (Term × Term)) : Prop where
  de : DE (level t n).E (.map T)
  pts : ∀ v : PN t n, denD (.map T) v → (d = "atom" ∧ v.1.1 = "atom") ∨ (v.1.1 ≠ "atom" ∧ ptKind v = d)
  wit : d ≠ "atom" → ∃ v : PN t n, denD (.map T) v ∧ ptKind v = d
  atoms : d = "atom" → ∀ q, denD (.map T) (aPt (t := t) (n := n) q)

theorem kind_bit (i : Nat) (hi : i < 8) : KindT t n (bitKind i) [(.atom "bitmap", .integer ((2 ^ i : Nat) : Int))] := by
  have pos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have le : 2 ^ i ≤ 255 := by
    have : 2 ^ i ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have bk : bitKind i ≠ "atom" := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind]
  refine ⟨single_de (by simp [names]) (Or.inl ⟨rfl, _, rfl, pos, le⟩), fun v hv => ?_, fun _ => ⟨bPt i hi, ?_, rfl⟩,
    fun h => absurd h bk⟩
  · obtain ⟨hb, hd⟩ := (denD_single _ _ v).mp hv
    rw [dn_bitmap, bitOf] at hd
    simp only [Int.toNat_natCast, Nat.testBit_two_pow, decide_eq_true_eq] at hd
    refine Or.inr ⟨by rw [hb]; decide, by simp [ptKind, hb, ← hd]⟩
  · rw [denD_single]
    simp only [bPt, dn_bitmap, bitOf, Int.toNat_natCast, Nat.testBit_two_pow_self, and_self]

theorem kind_atom : KindT t n "atom" [(.atom "atom", .tuple #[.atom "negation", .map []])] := by
  refine ⟨single_de (by simp [names]) (Or.inr (Or.inl ⟨rfl, ⟨Bool.false, [], rfl, by simp [Erlang.sets.elements?]⟩, .nil,
    by simp [amemV, mapLookup]⟩)), fun v hv => Or.inl ⟨rfl, ((denD_single _ _ v).mp hv).1⟩, fun h => absurd rfl h, fun _ q => ?_⟩
  rw [denD_single]
  simp [aPt, dn_atom, amemV, mapLookup]

theorem kind_fun : KindT t n "fun" [(.atom "fun", funTopT)] := by
  obtain ⟨a, ρ, rρ, fv⟩ := fVal_wit (E := (level t n).E) (den := (level t n).den)
  let w : PN t n := ⟨("fun", (0, a, ρ)), by simp [names],
    ⟨rρ, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun _ => fv⟩⟩
  refine ⟨single_de (by simp [names]) (Or.inr (Or.inr (Or.inl ⟨rfl, funA_top⟩))), fun v hv => ?_,
    fun _ => ⟨w, (denD_single _ _ w).mpr ⟨rfl, dn_funTop _⟩, rfl⟩, fun h => by simp at h⟩
  have hf := ((denD_single _ _ v).mp hv).1
  exact Or.inr ⟨by rw [hf]; decide, by simp [ptKind, hf]⟩

theorem kind_map : KindT t n "map" [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])] := by
  refine ⟨mapTop_de, fun v hv => ?_, fun _ => ⟨mpt (fun _ => none), (mapTop_den _).mpr rfl, rfl⟩,
    fun h => by simp at h⟩
  have hm := (mapTop_den v).mp hv
  exact Or.inr ⟨by rw [hm]; decide, by simp [ptKind, hm]⟩

theorem kind_tuple : KindT t n "tuple" [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])] := by
  refine ⟨tupleTop_de, fun v hv => ?_, fun _ => ⟨tpt [], (tupleTop_den _).mpr rfl, rfl⟩, fun h => by simp at h⟩
  have hm := (tupleTop_den v).mp hv
  exact Or.inr ⟨by rw [hm]; decide, by simp [ptKind, hm]⟩

theorem non_empty_list_top (m : Nat) : Elixir.Module.Types.Descr.«non_empty_list/2» (D m) (.atom "term") (.atom "term") =
    .ok (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) := by
  simp [Elixir.Module.Types.Descr.«non_empty_list/2», Elixir.Module.Types.Descr.«list_descr/3»,
    Elixir.Module.Types.Descr.«split_dynamic/1», Elixir.Module.Types.Descr.«list_descr_static/3», Erlang.erlang.«==/2»,
    Lynx.Except.orElse, Term.compare_step, Compare.compareStep]

theorem kind_list {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom "list") = .ok (.map T) ∧ KindT t n "list" T := by
  have b2 := kind_bit (t := t) (n := n) 2 (by omega)
  simp only [show ((2 ^ 2 : Nat) : Int) = 4 from rfl] at b2
  have dl : DE (level t n).E (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) :=
    single_de (by simp [names]) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr
      ⟨46675407, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩))))
  obtain ⟨U, rU, dU, sU⟩ := union_map b2.de dl hm
  refine ⟨U, ?_, ⟨dU, fun v hv => ?_, fun _ => ⟨bPt 2 (by omega), (sU _).mpr (Or.inl ?_), rfl⟩, fun h => by simp at h⟩⟩
  · simp [Elixir.STTDescrProofsTest.«kind_type/1», Elixir.Module.Types.Descr.«empty_list/0»,
      Elixir.Module.Types.Descr.«term/0», non_empty_list_top, rU]
  · rcases (sU v).mp hv with h | h
    · rcases b2.pts v h with ⟨e, -⟩ | ⟨ne, pk⟩
      · simp [bitKind] at e
      · exact Or.inr ⟨ne, pk⟩
    · have hl := ((denD_single _ _ v).mp h).1
      exact Or.inr ⟨by rw [hl]; decide, by simp [ptKind, hl]⟩
  · exact (denD_single _ _ _).mpr ⟨rfl, by simp only [bPt, dn_bitmap, bitOf]; decide⟩

/-- The key types of the spec's kinds. -/
theorem kind_run {d : String} (hd : d ∈ domainKinds) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom d) = .ok (.map T) ∧ KindT t n d T := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, kind_atom⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 0 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 1 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 4 (by omega)⟩
  · exact ⟨_, rfl, kind_fun⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 3 (by omega)⟩
  · exact kind_list hm
  · exact ⟨_, rfl, kind_map⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 5 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 6 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 7 (by omega)⟩
  · exact ⟨_, rfl, kind_tuple⟩

end

end Elixir.STTDescrProofsTest.Nest
