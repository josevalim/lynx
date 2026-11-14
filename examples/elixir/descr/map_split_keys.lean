namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The keys a split of keys selects: its atoms, the atoms outside its negated set, if any, and the keys of its
domain kinds. -/
def SplitKey (rs : List Term) (neg : Term) (ds : List Term) : MKey → Prop
  | .atom s => .atom s ∈ rs ∨ ∃ N, neg = .map N ∧ mapLookup N (.atom s) = none
  | .dom k _ => .atom (domKind k) ∈ ds

/-- Splits of static keys: atoms, a negated set of atoms or `nil`, and domain kinds, with the atom kind exactly when
atoms are negated. -/
structure SplitOk (rs : List Term) (neg : Term) (ds : List Term) : Prop where
  hrs : ∀ r ∈ rs, ∃ s, r = .atom s
  hneg : neg = .atom "nil" ∨ ∃ N, neg = .map N
  hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s
  hatom : .atom "atom" ∈ ds ↔ ∃ N, neg = .map N

theorem domKind_of {s : String} (h : s ∈ domainKinds) (ne : s ≠ "atom") : ∃ k, domKind k = s := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl ne
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩

theorem domKind_ne_atom (k : Fin 11) : domKind k ≠ "atom" := by
  revert k; decide

/-- Values a tag allows at the keys of a kind are those of the type it gives them. -/
theorem tagSem_some (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (kind : String) (x : V) :
    TagSem den tag kind (some x) ↔ den (tagType tag kind) x := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · simp [TagSem, tagType, ef.den_term]
  · simp [TagSem, tagType]
    exact fun h => ef.den_none x h
  · rw [tagSem_dom_iff (fun v h => ef.den_none v h), tagType_dom]
    cases mapLookup dl (.atom kind) <;> simp
    exact fun h' => ef.den_none x h'

def atomStrs (R : List Term) : List String := R.filterMap fun r => match r with
  | .atom s => some s
  | _ => none

theorem mem_atomStrs {R : List Term} {s : String} (h : .atom s ∈ R) : s ∈ atomStrs R :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- The keys of the fields of a line. -/
def lineKeys (L : Term) : List String :=
  match L with
  | .tuple ⟨[_, f, _]⟩ => keyStrs (domFields f)
  | _ => []

theorem lineKeys_eq (tag : Term) (l : List (Term × Term)) (negs : List Term) :
    lineKeys (.tuple #[tag, fieldsTerm l, Term.list negs]) = keyStrs l := by
  simp [lineKeys, domFields_fieldsTerm]

theorem lookup_entries_atom {es : List (Term × Term)} {s : String} {v : Term} (h : (Term.atom s, v) ∈ es) :
    .atom s ∈ (mapEntries es).map Prod.fst := by
  have hl : (mapLookup es (.atom s)).isSome := by
    rw [mapLookup]
    cases e : es.find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
    | none => exact absurd h (by simpa using List.find?_eq_none.mp e (.atom s, v))
    | some _ => simp
  rw [← mapLookup_mapEntries, mapLookup] at hl
  cases e : (mapEntries es).find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
  | none => rw [e] at hl; cases hl
  | some r =>
    have mr := List.mem_of_find?_eq_some e
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    exact List.mem_map.mpr ⟨r, mr, (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm this)⟩

/-- `map_keys_from_negated_set/2` on a map type: atoms outside the negated set, beyond which the maps of the type
hold the same values at any two atom keys outside the set. -/
theorem neg_keys (ef : EF nd E V den tl K) (N : List (Term × Term)) (m : Nat) {b : Term} (fb : MField E b) :
    ∃ R, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (m + 1)) (.map N) b = .ok (Term.list R) ∧
      (∀ r ∈ R, ∃ s, r = .atom s ∧ mapLookup N (.atom s) = none) ∧
      ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R → .atom c ∉ R →
        ∀ w, denMF E den b (swapW s c w) = denMF E den b w := by
  rcases fb with ⟨k, rfl⟩ | wb
  · refine ⟨[], ?_, by simp, fun s c _ _ _ _ w => by rw [denMF_top, denMF_top]⟩
    simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Elixir.Module.Types.Descr.«bdd_reduce/3»,
      Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-1-/2».pure,
      Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-1-/3», Erlang.orddict.«fold/3»,
      Erlang.erlang.«is_function/2», Erlang.maps.«keys/1»]
  obtain ⟨new, run, hn, hk⟩ := neg_reduce N m wb []
  refine ⟨(mapEntries new).map Prod.fst, ?_, fun r mr => ?_, fun s c sN cN ns nc w => ?_⟩
  · simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», run, Erlang.maps.«keys/1»]
  · obtain ⟨e, me, rfl⟩ := List.mem_map.mp mr
    obtain ⟨s, rfl, hs⟩ := hn e (mem_of_mem_mapEntries me)
    exact ⟨s, rfl, hs⟩
  · rw [denMF_bdd wb, denMF_bdd wb]
    refine eval_ext hk fun t ⟨lt, nt⟩ => ?_
    obtain ⟨k, tag, l, rfl, -, -⟩ := lt.1
    have fresh : ∀ a, mapLookup N (.atom a) = none → .atom a ∉ (mapEntries new).map Prod.fst →
        mapLookup l (.atom a) = none := fun a aN na =>
      lookup_fresh' fun ma => na (lookup_entries_atom (nt k tag l rfl a ma aN))
    have lit : MapLitV E (.tuple #[.integer k, tag, fieldsTerm l]) := lt.1
    rw [Bool.eq_iff_iff, valM_iff ef.mopsE ef.mdopsE ef.semR lit, valM_iff ef.mopsE ef.mdopsE ef.semR lit, nsem_lit,
      nsem_lit, msem_swapW_iff (fresh s sN ns) (fresh c cN nc)]

/-- Values at an atom key outside a negated set and the keys a map type names are values its lines allow at atoms
outside their fields. -/
theorem unnamed_tag (ef : EF nd E V den tl K) {b : Term} {N : List (Term × Term)} {R : List Term} (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w)
    (swap : ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R → .atom c ∉ R →
      ∀ w, denMF E den b (swapW s c w) = denMF E den b w)
    {s : String} (sN : mapLookup N (.atom s) = none) (sR : .atom s ∉ R) {w : MW V} {x : V}
    (hw : denMF E den b w = Bool.true) (hx : w (.atom s) = some x) : ∃ L ∈ lines, LineTag den L "atom" x := by
  obtain ⟨c, hc⟩ := fresh_str (s :: keyStrs N ++ atomStrs R ++ lines.flatMap lineKeys)
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap, not_or] at hc
  obtain ⟨cs, ⟨cN, cR⟩, cL⟩ := hc
  have cN' : mapLookup N (.atom c) = none := lookup_fresh' cN
  have cR' : .atom c ∉ R := fun m => cR (mem_atomStrs m)
  have hw' : denMF E den b (swapW s c w) = Bool.true := by rw [swap s c sN cN' sR cR']; exact hw
  obtain ⟨L, mL, hL⟩ := (sl _).mp hw'
  obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
  have hm := (inMLine_iff.mp hL).1.atoms c
  have lc : mapLookup l (.atom c) = none := lookup_fresh' fun m => cL ⟨_, mL, by rw [lineKeys_eq]; exact m⟩
  unfold FSem at hm
  rw [lc] at hm
  have sw : swapW s c w (.atom c) = some x := by
    unfold swapW; simp [show MKey.atom c ≠ MKey.atom s from fun e => cs (MKey.atom.inj e), hx]
  rw [sw] at hm
  exact ⟨_, mL, tag, l, negs, rfl, (tagSem_some ef g "atom" x).mp hm⟩

/-- Values a line allows at the keys of a kind occur at such a key in a map of the line, outside a negated set of
atoms for the atom kind. -/
theorem tag_witness (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) (ne : ∃ w, InMLine den L w) {kind : String}
    (hk : kind ∈ domainKinds) {x : V} (hx : LineTag den L kind x) (N : List (Term × Term)) :
    ∃ w, InMLine den L w ∧ ∃ κ, ((kind = "atom" ∧ ∃ c, κ = .atom c ∧ mapLookup N (.atom c) = none) ∨
      ∃ k i, kind = domKind k ∧ κ = .dom k i) ∧ w κ = some x := by
  obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hL
  obtain ⟨tag', l', negs', e, hx⟩ := hx
  obtain ⟨rfl, -, -⟩ := tuple3_inj e
  obtain ⟨w₀, h₀⟩ := ne
  have hs := (tagSem_some ef g kind x).mpr hx
  by_cases ka : kind = "atom"
  · subst ka
    let M := ((keyStrs l ++ keyStrs N).map String.length).foldr max 0
    have fr : ∀ c ∈ freshStrs M (negs.length + 1), c ∉ keyStrs l ++ keyStrs N := fun c mc m => by
      have := le_maxLen _ c m; have := freshStrs_len mc; omega
    obtain ⟨κ, mκ, w, hw, wκ⟩ := line_witness h₀ ((freshStrs M (negs.length + 1)).map MKey.atom)
      (List.Pairwise.map MKey.atom (fun _ _ ne e => ne (MKey.atom.inj e)) (freshStrs_nodup M _)) (by simp [freshStrs_length]) fun κ mκ => by
        obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
        have lc : mapLookup l (.atom c) = none := lookup_fresh' fun m => fr c mc (List.mem_append_left _ m)
        show FSem den tag l c (some x)
        unfold FSem; rw [lc]; exact hs
    obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
    exact ⟨w, hw, .atom c, Or.inl ⟨rfl, c, rfl, lookup_fresh' fun m => fr c mc (List.mem_append_right _ m)⟩, wκ⟩
  · obtain ⟨k, rfl⟩ := domKind_of hk ka
    obtain ⟨κ, mκ, w, hw, wκ⟩ := line_witness h₀ ((List.range (negs.length + 1)).map (MKey.dom k))
      (List.Pairwise.map (MKey.dom k) (fun _ _ ne e => ne (MKey.dom.inj e).2) List.nodup_range) (by simp) fun κ mκ => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp mκ
        exact hs
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp mκ
    exact ⟨w, hw, .dom k i, Or.inr ⟨k, i, rfl, rfl⟩, wκ⟩

/-- `map_get_static_dnf/3` on the non-empty lines of a map type and a split of static keys unites the values its maps
hold at the keys the split selects. -/
theorem get_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) {b : Term} (fb : MField E b) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rs : List Term} {neg : Term}
    {ds : List Term} (hs : SplitOk rs neg ds) :
    ∃ T, Elixir.Module.Types.Descr.«map_get_static_dnf/3» (D (n + 4)) b (Term.list lines)
        (.tuple #[Term.list rs, .nil, neg, Term.list ds, .nil]) = .ok T ∧ E T ∧
      ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨T₂, r₂, h₂, s₂⟩ := get_keys ef hn lines hl rs hs.hrs ef.none
  obtain ⟨T₃, r₃, h₃, s₃⟩ := get_keys ef hn lines hl [] (by simp) h₂
  obtain ⟨R, rR, hR, swR⟩ : ∃ R, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 4)) neg b =
      .ok (Term.list R) ∧ (∀ r ∈ R, ∃ s, r = .atom s ∧ ∃ N, neg = .map N ∧ mapLookup N (.atom s) = none) ∧
      ∀ N, neg = .map N → ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R →
        .atom c ∉ R → ∀ w, denMF E den b (swapW s c w) = denMF E den b w := by
    rcases hs.hneg with rfl | ⟨N, rfl⟩
    · exact ⟨[], by simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»], by simp, fun N e => by cases e⟩
    · obtain ⟨R, rR, hR, swR⟩ := neg_keys ef N (n + 3) fb
      exact ⟨R, rR, fun r mr => let ⟨s, e, h⟩ := hR r mr; ⟨s, e, N, rfl, h⟩, fun N' e => by cases e; exact swR⟩
  obtain ⟨T₄, r₄, h₄, s₄⟩ := get_keys ef hn lines hl R (fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩) h₃
  obtain ⟨T₅, r₅, h₅, s₅⟩ := get_domains ef hn lines hl' ds (fun d md => let ⟨s, _, e⟩ := hs.hds d md; ⟨s, e⟩) h₄
  refine ⟨T₅, ?_, h₅, fun x => ?_⟩
  · have nil : Erlang.lists.«foldl/3» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-1-" 2 #[Term.list lines]) T₅ .nil = .ok T₅ := by
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
    simp only [Term.list] at r₃
    simp [Elixir.Module.Types.Descr.«map_get_static_dnf/3», r₂, r₃, rR, r₄, r₅, nil]
  rw [s₅, s₄, s₃, s₂]
  constructor
  · rintro ((((h | ⟨s, ms, L, mL, w, hw, hx⟩) | ⟨s, ms, -⟩) | ⟨s, ms, L, mL, w, hw, hx⟩) | ⟨kind, mk, L, mL, hx⟩)
    · exact absurd h (ef.den_none x)
    · exact ⟨w, (sl w).mpr ⟨L, mL, hw⟩, .atom s, Or.inl ms, hx⟩
    · simp at ms
    · obtain ⟨s', e, N, eN, hN⟩ := hR _ ms
      obtain rfl : s = s' := Term.atom.inj e
      exact ⟨w, (sl w).mpr ⟨L, mL, hw⟩, .atom s, Or.inr ⟨N, eN, hN⟩, hx⟩
    · obtain ⟨k₀, hk, ek⟩ := hs.hds _ mk
      cases ek
      obtain ⟨N, eN⟩ : ∃ N, (kind = "atom" → neg = .map N) := by
        by_cases ka : kind = "atom"
        · subst ka; obtain ⟨N, eN⟩ := hs.hatom.mp mk; exact ⟨N, fun _ => eN⟩
        · exact ⟨[], fun e => absurd e ka⟩
      obtain ⟨w, hw, κ, hκ, wκ⟩ := tag_witness ef (hl L mL).1 (hl L mL).2 hk hx N
      refine ⟨w, (sl w).mpr ⟨L, mL, hw⟩, κ, ?_, wκ⟩
      rcases hκ with ⟨ka, c, rfl, hc⟩ | ⟨k, i, rfl, rfl⟩
      · exact Or.inr ⟨N, eN ka, hc⟩
      · exact mk
  · rintro ⟨w, hw, κ, sk, hx⟩
    obtain ⟨L, mL, hL⟩ := (sl w).mp hw
    cases κ with
    | atom s =>
      rcases sk with ms | ⟨N, eN, hN⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨s, ms, L, mL, w, hL, hx⟩)))
      · by_cases sR : .atom s ∈ R
        · exact Or.inl (Or.inr ⟨s, sR, L, mL, w, hL, hx⟩)
        · obtain ⟨L', mL', ht⟩ := unnamed_tag ef lines hl' sl (swR N eN) hN sR hw hx
          exact Or.inr ⟨"atom", hs.hatom.mpr ⟨N, eN⟩, L', mL', ht⟩
    | dom k i =>
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl' L mL
      have := (inMLine_iff.mp hL).1.doms k i
      rw [hx] at this
      exact Or.inr ⟨domKind k, sk, _, mL, tag, l, negs, rfl, (tagSem_some ef g _ x).mp this⟩

end

end Elixir.STTDescrProofsTest.Nest
