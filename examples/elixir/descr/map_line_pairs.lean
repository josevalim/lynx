namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem foldl1_err {m : Nat} (f : Term) (R : List Term → Term → Prop) (Q : Term → Prop) (e : Exception)
    (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → (∃ a', R (pre ++ [x]) a' ∧ (D m).pure f #[x, a] = .ok a') ∨
      (Q x ∧ (D m).pure f #[x, a] = .error e)) :
    ∀ (rest pre : List Term) acc, (∀ x ∈ rest, x ∈ l) → R pre acc →
      (∃ r, R (pre ++ rest) r ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r) ∨
        (∃ x ∈ rest, Q x ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .error e) := by
  intro rest
  induction rest with
  | nil => intro pre acc _ h; exact Or.inl ⟨acc, by simpa using h, by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc sub h
    rcases step pre x acc (sub x List.mem_cons_self) h with ⟨a', h', run⟩ | ⟨q, run⟩
    · rcases ih (pre ++ [x]) a' (fun y my => sub y (List.mem_cons_of_mem _ my)) h' with ⟨r, hr, rest⟩ | ⟨y, my, q, rest⟩
      · refine Or.inl ⟨r, by simpa using hr, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only at rest ⊢
        simp only [run, Lynx.Except.ok_bind]
        exact rest
      · refine Or.inr ⟨y, List.mem_cons_of_mem _ my, q, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only at rest ⊢
        simp only [run, Lynx.Except.ok_bind]
        exact rest
    · refine Or.inr ⟨x, List.mem_cons_self, q, ?_⟩
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [run]
      rfl

/-- Folds whose steps either keep a relation or fail with an exception. -/
theorem foldl_err {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (Q : Term → Prop)
    (e : Exception) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → (∃ a', R (pre ++ [x]) a' ∧ (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') ∨
      (Q x ∧ (D m).pure (.function mo nm 2 caps) #[x, a] = .error e)) (acc : Term) (h : R [] acc) :
    (∃ r, R l r ∧ Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r) ∨
      (∃ x ∈ l, Q x ∧ Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .error e) := by
  have run := foldl1_err (.function mo nm 2 caps) R Q e l step l [] acc (fun _ h => h) h
  have eq : Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) =
      Erlang.lists.«foldl_1/3» (D m) (.function mo nm 2 caps) acc (Term.list l) := by
    cases l with
    | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»]
    | cons x xs =>
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list]
      rw [Erlang.lists.«foldl_1/3».eq_def]
  rw [eq]
  simpa using run

section
variable {t : Term} {n : Nat}

/-- Points of pairs of a value of each of two types. -/
def PairPt (t : Term) (n : Nat) (a b : Term) (p : PN t n) : Prop :=
  ∃ w : List (level t n).V, (∀ X, denD (.map X) p ↔ TT t n X w) ∧
    ∃ x y, w = [x, y] ∧ (level t n).den a x ∧ (level t n).den b y

/-- `tuple/1` of two element types holds the pairs of their values. -/
theorem pair_run {a b : Term} (ha : (level t n).E a) (hb : (level t n).E b) (hsa : Static a) (hsb : Static b) :
    ∃ P, Elixir.Module.Types.Descr.«tuple/1» (Term.list [a, b]) = .ok P ∧ DE (level t n).E P ∧
      ∀ p : PN t n, denD P p ↔ PairPt t n a b p := by
  obtain ⟨P, run, dP, sP⟩ := pair_sem ha hb hsa hsb
  obtain ⟨k, run', -⟩ := tuple_run [a, b] (by simp [hsa, hsb])
  rw [run] at run'
  cases run'
  refine ⟨_, run, dP, fun p => ?_⟩
  constructor
  · intro hp
    have ht : p.1.1 = "tuple" := by
      rw [denD_map] at hp
      by_cases h : p.1.1 = "tuple"
      · exact h
      · simp [mapLookup, h, dn_none] at hp
    obtain ⟨w, hw⟩ := pt_tuple p ht
    exact ⟨w, hw, (sP w).mp ⟨_, rfl, (hw _).mp hp⟩⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨X, e, hX⟩ := (sP w).mpr h
    cases e
    exact (hw _).mpr hX

end

section
variable {t : Term} {n : Nat}

theorem bitKind_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : bitKind i = bitKind j) : i = j := by
  match i, hi, j, hj with
  | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ | 4, _, 4, _ | 5, _, 5, _ | 6, _, 6, _ | 7, _, 7, _ => rfl
  | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _
  | 1, _, 0, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _
  | 2, _, 0, _ | 2, _, 1, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _
  | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _
  | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _
  | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 6, _ | 5, _, 7, _
  | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 7, _
  | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ => simp [bitKind] at h

/-- Types of the keys of a kind, as `domain_key_to_descr/1` gives them: all points of that kind. -/
structure DomT (t : Term) (n : Nat) (d : String) (T : Term) : Prop where
  de : DE (level t n).E T
  static : Static T
  atoms : d = "atom" → ∀ v : PN t n, v.1.1 = "atom" → denD T v
  kinds : d ≠ "atom" → ∀ v : PN t n, ptKind v = d → denD T v

theorem domT_bit (i : Nat) (hi : i < 8) (ni : i ≠ 2) :
    DomT t n (bitKind i) (.map [(.atom "bitmap", .integer ((2 ^ i : Nat) : Int))]) := by
  have kb := kind_bit (t := t) (n := n) i hi
  refine ⟨kb.de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => absurd h ?_, fun _ v hv => ?_⟩
  · match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind]
  rw [denD_single]
  by_cases hb : v.1.1 = "bitmap"
  · have hp : v.1.2.1 < 8 := v.2.2.2.1 hb
    have := bitKind_inj hp hi (by simpa [ptKind, hb] using hv)
    refine ⟨hb, ?_⟩
    simp only [dn_bitmap, bitOf, Int.toNat_natCast, this, Nat.testBit_two_pow_self]
  · exfalso
    have hn := v.2.1
    simp only [ptKind, hb, ite_false] at hv
    rw [hv] at hn
    match i, hi, ni with
    | 0, _, _ | 1, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ => simp [bitKind, names] at hn

end

section
variable {t : Term} {n : Nat}

theorem bitKind_mem (i : Nat) : bitKind i ∈ ["binary", "bitstring_no_binary", "list", "integer", "float", "pid", "port",
    "reference"] := by
  unfold bitKind; split <;> simp

/-- Points of a kind outside the bitmap kinds are of that field. -/
theorem ptKind_field {v : PN t n} {d : String} (h : ptKind v = d) (hd : d = "atom" ∨ d = "fun" ∨ d = "map" ∨ d = "tuple") :
    v.1.1 = d := by
  unfold ptKind at h
  split at h
  · have := bitKind_mem v.1.2.1
    rw [h] at this
    rcases hd with rfl | rfl | rfl | rfl <;> simp at this
  · exact h

theorem domT_list : DomT t n "list"
    (.map [(.atom "bitmap", .integer 4), (.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) := by
  have fl : FieldC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) "list"
      (.tuple #[.integer 46675407, .atom "term", .atom "term"]) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr ⟨_, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩)))
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩),
    fun h => by simp at h, fun _ v hv => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
    by_cases e : compareExact (fuel q (.atom "bitmap")) q (.atom "bitmap") = .eq
    · exact ⟨"bitmap", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · by_cases e' : compareExact (fuel q (.atom "list")) q (.atom "list") = .eq
      · exact ⟨"list", by simp [names], (compareExact_eq_atom _ _).mp e'⟩
      · simp [e, e'] at h
  · rw [lookup_cons_atom, lookup_cons_atom] at h
    by_cases e : "bitmap" = name
    · subst e; simp at h; subst h; exact Or.inl ⟨rfl, 4, rfl, by omega, by omega⟩
    · by_cases e' : "list" = name
      · subst e'; simp at h; subst h; exact fl
      · simp [e, e', mapLookup] at h
  · rw [denD_map]
    unfold ptKind at hv
    split at hv
    · rename_i hb
      have hp : v.1.2.1 < 8 := v.2.2.2.1 hb
      have : v.1.2.1 = 2 := bitKind_inj hp (by omega) hv
      rw [hb]
      simp [mapLookup, dn_bitmap, bitOf, this]
      decide
    · rw [hv]
      simp [mapLookup, dn_list, denL, isListTop]

/-- `domain_key_to_descr/1` gives every point of a kind. -/
theorem dkd_run {d : String} (hd : d ∈ domainKinds) :
    ∃ T, Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) = .ok T ∧ DomT t n d T := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, rfl, kind_atom.de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun _ v hv => ?_,
      fun h => absurd rfl h⟩
    rw [denD_single]; exact ⟨hv, by simp [dn_atom, amemV, mapLookup]⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 0 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 1 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 4 (by omega) (by omega)⟩
  · refine ⟨_, rfl, kind_fun.de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => by simp at h,
      fun _ v hv => ?_⟩
    rw [denD_single]; exact ⟨ptKind_field hv (by simp), dn_funTop _⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 3 (by omega) (by omega)⟩
  · exact ⟨_, rfl, domT_list⟩
  · refine ⟨_, rfl, mapTop_de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => by simp at h,
      fun _ v hv => (mapTop_den v).mpr (ptKind_field hv (by simp))⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 5 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 6 (by omega) (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using domT_bit (t := t) (n := n) 7 (by omega) (by omega)⟩
  · refine ⟨_, rfl, tupleTop_de, Or.inr (Or.inl ⟨_, rfl, by simp [mapLookup]⟩), fun h => by simp at h,
      fun _ v hv => (tupleTop_den v).mpr (ptKind_field hv (by simp))⟩

end

/-- The pair function `map_to_list/1` passes. -/
def mtlF : Term := .function "Elixir.Module.Types.Descr" "-map_to_list/1-fun-0-" 2 #[]

/-- The type `domain_key_to_descr/1` gives a kind. -/
def dkdT (d : String) : Term :=
  match Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) with
  | .ok T => T
  | .error _ => .map []

section
variable {t : Term} {n : Nat}

theorem dkdT_run {d : String} (hd : d ∈ domainKinds) :
    Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) = .ok (dkdT d) ∧ DomT t n d (dkdT d) := by
  obtain ⟨T, run, hT⟩ := dkd_run (t := t) (n := n) hd
  have e : dkdT d = T := by simp [dkdT, run]
  rw [e]
  exact ⟨run, hT⟩

/-- Pairs of key and value types, as the pair function of `map_to_list/1` builds them. -/
theorem mtl_pair {a b : Term} (ha : (level t n).E a) (hb : (level t n).E b) (hsa : Static a) (hsb : Static b)
    (m : Nat) : ∃ P, (D m).pure mtlF #[a, b] = .ok P ∧ DE (level t n).E P ∧
      ∀ p : PN t n, denD P p ↔ PairPt t n a b p := by
  obtain ⟨P, run, dP, sP⟩ := pair_run ha hb hsa hsb
  refine ⟨P, ?_, dP, sP⟩
  rw [mtlF, Erlang.program.«Elixir.Module.Types.Descr:-map_to_list/1-fun-0-/2».pure]
  simpa [Elixir.Module.Types.Descr.«-map_to_list/1-fun-0-/2»] using run

/-- Pairs of the domains of a tag with values. -/
def DomPair (t : Term) (n : Nat) (dl : List (Term × Term)) (p : PN t (n + 1)) : Prop :=
  ∃ d v, (Term.atom d, v) ∈ dl ∧ d ∈ domainKinds ∧ (∃ x, (level t (n + 1)).den v x) ∧
    PairPt t (n + 1) (dkdT d) v p

/-- `orddict:fold/3` of `map_to_list_static/3` over domains unites the pairs of their kinds and non-empty types. -/
theorem dom_pairs {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) : ∀ (dl : List (Term × Term)),
    DomsV (level t (n + 1)).E dl → ∀ acc, DE (level t (n + 1)).E acc →
    ∃ acc', Erlang.orddict.«fold/3» (D (M + 1))
        (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-0-" 3 #[mtlF]) acc (fieldsTerm dl) = .ok acc' ∧
      DE (level t (n + 1)).E acc' ∧ ∀ p, denD acc' p ↔ denD acc p ∨ DomPair t n dl p
  | [], _, acc, ha => ⟨acc, by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], ha, fun p => by simp [DomPair]⟩
  | (k, v) :: rest, dv, acc, ha => by
    obtain ⟨⟨d, rfl, md⟩, hv⟩ := dv.1 _ List.mem_cons_self
    have dv' : DomsV (level t (n + 1)).E rest := ⟨fun e me => dv.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp dv.2).2⟩
    obtain ⟨T, rT, hT⟩ : ∃ T, Elixir.Module.Types.Descr.«domain_key_to_descr/1» (.atom d) = .ok T ∧ T = dkdT d :=
      ⟨_, (dkdT_run (t := t) (n := n) md).1, rfl⟩
    subst hT
    have dT := (dkdT_run (t := t) (n := n) md).2
    obtain ⟨eb, reb, seb⟩ := (level t (n + 1)).ef.empty_pub hv
    have step : ∃ a', Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-0-/4» (D M) mtlF (.atom d) v acc = .ok a' ∧
        DE (level t (n + 1)).E a' ∧ ∀ p, denD a' p ↔ denD acc p ∨
          ((∃ x, (level t (n + 1)).den v x) ∧ PairPt t (n + 1) (dkdT d) v p) := by
      cases eb
      · obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) (e_succ dT.de) hv dT.static
          ((level t (n + 1)).ef.static hv) M
        obtain ⟨c, hc, rc, sc⟩ := (ef_next t (n + 1)).opt_union [] ha dP (m := M) hM
        refine ⟨c, ?_, hc, fun p => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-0-/4», reb M (by rw [level_K] at hM ⊢; omega),
            Lynx.Term.isMember, boolAtom, rT, rP, Elixir.Module.Types.Descr.«opt_union/2», rc]
        · rw [sc, sP]
          have ne : ∃ x, (level t (n + 1)).den v x := Classical.byContradiction fun h =>
            absurd (seb.mpr fun x hx => h ⟨x, hx⟩) (by simp)
          simp [ne]
      · refine ⟨acc, ?_, ha, fun p => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-0-/4», reb M (by rw [level_K] at hM ⊢; omega),
            Lynx.Term.isMember, boolAtom]
        · have ne : ¬∃ x, (level t (n + 1)).den v x := fun ⟨x, hx⟩ => seb.mp rfl x hx
          simp [ne]
    obtain ⟨a', ra, da, sa⟩ := step
    obtain ⟨acc', run, dacc, sacc⟩ := dom_pairs hM rest dv' a' da
    refine ⟨acc', ?_, dacc, fun p => ?_⟩
    · rw [Erlang.orddict.«fold/3».eq_def]
      simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-0-/3».pure, ra, run]
    · rw [sacc, sa]
      simp only [DomPair, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ((h | ⟨ne, h⟩) | ⟨d', v', m', hd', ne', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨d, v, Or.inl ⟨rfl, rfl⟩, md, ne, h⟩
        · exact Or.inr ⟨d', v', Or.inr m', hd', ne', h⟩
      · rintro (h | ⟨d', v', ⟨e₁, rfl⟩ | m', hd', ne', h⟩)
        · exact Or.inl (Or.inl h)
        · cases e₁; exact Or.inl (Or.inr ⟨ne', h⟩)
        · exact Or.inr ⟨d', v', m', hd', ne', h⟩

end

section
variable {t : Term} {n : Nat}

/-- Pairs that a line of a map type contributes through its domains. -/
def LinePairs (t : Term) (n : Nat) (L : Term) (p : PN t (n + 1)) : Prop :=
  ∃ (dl l : List (Term × Term)) (negs : List Term), L = .tuple #[fieldsTerm dl, fieldsTerm l, Term.list negs] ∧
    DomPair t n dl p

/-- Lines with an open tag. -/
def OpenLine (L : Term) : Prop := ∃ (l : Term) (negs : Term), L = .tuple #[.atom "open", l, negs]

theorem line_pairs_step {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {L : Term} (hL : MLine (level t (n + 1)).E L)
    {acc : Term} (ha : DE (level t (n + 1)).E acc) :
    (OpenLine L ∧ (D (M + 2)).pure (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF])
        #[L, acc] = .error (.throw (.atom "open"))) ∨
      (¬OpenLine L ∧ ∃ a', (D (M + 2)).pure (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF])
        #[L, acc] = .ok a' ∧ DE (level t (n + 1)).E a' ∧ ∀ p, denD a' p ↔ denD acc p ∨ LinePairs t n L p) := by
  obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hL
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_to_list_static/3-fun-1-/2».pure]
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · exact Or.inl ⟨⟨_, _, rfl⟩, by simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-1-/3»]⟩
  · refine Or.inr ⟨fun ⟨_, _, e⟩ => by simp at e, acc, ?_, ha, fun p => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-1-/3», Erlang.erlang.«is_list/1»]
    · simp only [LinePairs, iff_self_or]
      rintro ⟨dl, l', negs', e, -⟩
      obtain ⟨e₁, -, -⟩ := tuple3_inj e
      exact absurd e₁ (fieldsTerm_ne_atom dl "closed").symm
  · obtain ⟨a', run, da, sa⟩ := dom_pairs (t := t) (n := n) (M := M) hM dl dv acc ha
    refine Or.inr ⟨fun ⟨_, _, e⟩ => (fieldsTerm_ne_atom dl "open") (tuple3_inj e).1, a', ?_, da, fun p => ?_⟩
    · have ne := fieldsTerm_ne_atom dl
      have il := is_list_fieldsTerm dl
      generalize hT : fieldsTerm dl = T at ne il run
      rw [Elixir.Module.Types.Descr.«-map_to_list_static/3-fun-1-/3».eq_def]
      simp only
      split
      · exact absurd rfl (ne _)
      · simp [il, run]
    · rw [sa]
      refine or_congr Iff.rfl ⟨fun h => ⟨dl, l, negs, rfl, h⟩, fun ⟨dl', l', negs', e, h⟩ => ?_⟩
      obtain ⟨e₁, -, -⟩ := tuple3_inj e
      rwa [fieldsTerm_inj e₁]

end

section
variable {t : Term} {n : Nat}

/-- The fold of `map_to_list_static/3` over lines: the pairs of their domains, or `:open` thrown for an open line. -/
theorem lines_pairs {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L) :
    (∃ L ∈ lines, OpenLine L ∧ Erlang.lists.«foldl/3» (D (M + 2))
        (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF]) (.map []) (Term.list lines) =
          .error (.throw (.atom "open"))) ∨
      (∃ acc, Erlang.lists.«foldl/3» (D (M + 2))
        (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" 2 #[mtlF]) (.map []) (Term.list lines) =
          .ok acc ∧ (∀ L ∈ lines, ¬OpenLine L) ∧ DE (level t (n + 1)).E acc ∧
        ∀ p, denD acc p ↔ ∃ L ∈ lines, LinePairs t n L p) := by
  rcases foldl_err (m := M + 2) "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-1-" #[mtlF]
    (fun pre acc => (∀ L ∈ pre, ¬OpenLine L) ∧ DE (level t (n + 1)).E acc ∧
      ∀ p, denD acc p ↔ ∃ L ∈ pre, LinePairs t n L p) OpenLine (.throw (.atom "open")) lines
    (fun pre L a mL ⟨ho, ha, sa⟩ => by
      rcases line_pairs_step (t := t) (n := n) hM (hl L mL) ha with ⟨o, run⟩ | ⟨no, a', run, da, sa'⟩
      · exact Or.inr ⟨o, run⟩
      · refine Or.inl ⟨a', ⟨fun L' mL' => ?_, da, fun p => ?_⟩, run⟩
        · rcases List.mem_append.mp mL' with h | h
          · exact ho L' h
          · simp at h; subst h; exact no
        · rw [sa', sa]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro (⟨L', m', h⟩ | h)
            · exact ⟨L', Or.inl m', h⟩
            · exact ⟨L, Or.inr rfl, h⟩
          · rintro ⟨L', m' | rfl, h⟩
            · exact Or.inl ⟨L', m', h⟩
            · exact Or.inr h)
    (.map []) ⟨by simp, de_none, fun p => by simp [denD_map, mapLookup, dn_none]⟩ with
    ⟨r, ⟨ho, dr, sr⟩, run⟩ | ⟨L, mL, o, run⟩
  · exact Or.inr ⟨r, run, ho, dr, sr⟩
  · exact Or.inl ⟨L, mL, o, run⟩

end

end Elixir.STTDescrProofsTest.Nest
