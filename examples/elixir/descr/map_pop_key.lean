namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem fieldAt_ok (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (a : String) : FieldValue E (fieldAt tag l a) := by
  unfold fieldAt
  cases h : mapLookup l (.atom a) with
  | some f =>
    obtain ⟨e, me, rfl⟩ := lookup_mem h
    exact (sl.1 e me).2
  | none =>
    obtain ⟨f, run, hf⟩ := tag_field_ok ef.term ef.none g.plain
    rw [key_tag_field g] at run
    cases run
    exact hf

theorem mleaf_field {k : Int} {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (key : KeyOk (.tuple #[.integer k, tag, fieldsTerm l])) : MField E (.tuple #[.integer k, tag, fieldsTerm l]) := by
  by_cases top : tag = .atom "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, tag, l, rfl, g, sl⟩, ?_, key⟩)
    rintro ⟨k', e⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    exact top ⟨e₂, fieldsTerm_eq_nil.mp e₃⟩

/-- `map_pop_key_bdd/3` splits a map literal into a pair at a key. -/
theorem pop_pair (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (a : String) : ∃ k : Int, Elixir.Module.Types.Descr.«map_pop_key_bdd/3» tag (fieldsTerm l) (.atom a) =
      .ok (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]]) ∧
      MPairOk E (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]]) ∧
      (∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true ↔
        MSem den tag (eraseKey a l) w) ∧
      ∀ w, MSem den tag l w ↔ MPairIn E den (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]])
        (w (.atom a)) (eraseK a w) := by
  obtain ⟨k, run, key⟩ := pop_val g sl a
  have sl' := fieldsV_eraseKey (a := a) sl
  have rest : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true ↔
      MSem den tag (eraseKey a l) w := fun w => denMF_leaf ef sl' g w
  refine ⟨k, run, ⟨_, _, rfl, fieldAt_ok ef g sl a, mleaf_field g sl' key⟩, rest, fun w => ?_⟩
  rw [mpairIn_iff, rest, msem_at ef g]

theorem msem_open_nil (w : MW V) : MSem den (.atom "open") [] w :=
  ⟨fun s => by simp [FSem, TagSem, mapLookup], fun k i => by simp [TagSem]⟩

/-- Rests of negated pairs: single literals without the key. -/
def RestOk (E : Term → Prop) (den : Term → V → Prop) (a : String) (p : Term) : Prop :=
  ∃ (f : Term) (k : Int) (ntag : Term) (nl : List (Term × Term)), p = .tuple #[f, .tuple #[.integer k, ntag, fieldsTerm nl]] ∧ TagV E ntag ∧ FieldsV E nl ∧
    mapLookup nl (.atom a) = none ∧
    ∀ w, denMF E den (.tuple #[.integer k, ntag, fieldsTerm nl]) w = Bool.true ↔ MSem den ntag nl w

/-- `map_split_negative_pairs_key/3` splits negated literals at a key, unless one is the top literal. -/
theorem msplit_negs (ef : EF nd E V den tl K) (a : String) : ∀ (negs : List Term), (∀ N ∈ negs, MapLitV E N) →
    ∀ (acc : List Term), ∃ r, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3» (Term.list negs) (.atom a)
        (Term.list acc) = .ok r ∧
      ((r = .atom "empty" ∧ ∃ N ∈ negs, ∀ w, NSem den N w) ∨
        ∃ P, r = Term.list (P ++ acc) ∧ (∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) ∧
          ∀ w, (∃ N ∈ negs, NSem den N w) ↔ ∃ p ∈ P, MPairIn E den p (w (.atom a)) (eraseK a w))
  | [], _, acc => ⟨_, by rw [Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3».eq_def]; rfl,
      Or.inr ⟨[], by simp, by simp, fun w => by simp⟩⟩
  | N :: rest, lits, acc => by
    obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := lits _ List.mem_cons_self
    have lits' := fun N' (m : N' ∈ rest) => lits N' (List.mem_cons_of_mem _ m)
    by_cases top : ntag = .atom "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      refine ⟨_, ?_, Or.inl ⟨rfl, _, List.mem_cons_self, fun w => nsem_lit.mpr (msem_open_nil w)⟩⟩
      rw [Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3».eq_def]
      rfl
    obtain ⟨k', run, ok, rest', sem⟩ := pop_pair (den := den) ef gn snl a
    obtain ⟨r, rr, h⟩ := msplit_negs ef a rest lits'
      (.tuple #[fieldAt ntag nl a, .tuple #[.integer k', ntag, fieldsTerm (eraseKey a nl)]] :: acc)
    have step : Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3»
        (Term.list (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest)) (.atom a) (Term.list acc) =
        Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3» (Term.list rest) (.atom a)
          (Term.list (.tuple #[fieldAt ntag nl a, .tuple #[.integer k', ntag, fieldsTerm (eraseKey a nl)]] :: acc)) := by
      rw [Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3».eq_def]
      simp only [Term.list]
      split
      · rename_i heq
        obtain ⟨h₁, -⟩ := Term.cons.inj heq
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj h₁
        exact absurd ⟨e₂, fieldsTerm_eq_nil.mp e₃⟩ top
      · rename_i heq
        obtain ⟨h₁, rfl⟩ := Term.cons.inj heq
        obtain ⟨-, rfl, rfl⟩ := tuple3_inj h₁
        simp [run]
      · rename_i heq; cases heq
      · rename_i h₁ h₂ h₃; exact absurd rfl (h₂ _ _ _ _)
    refine ⟨r, step.trans rr, ?_⟩
    rcases h with ⟨rfl, N', mN', hN'⟩ | ⟨P, rfl, hP, sP⟩
    · exact Or.inl ⟨rfl, N', List.mem_cons_of_mem _ mN', hN'⟩
    refine Or.inr ⟨P ++ [.tuple #[fieldAt ntag nl a, .tuple #[.integer k', ntag, fieldsTerm (eraseKey a nl)]]], by simp,
      fun p mp => ?_, fun w => ?_⟩
    · rcases List.mem_append.mp mp with mp | mp
      · exact hP p mp
      · rw [List.mem_singleton] at mp; subst mp
        refine ⟨ok, _, k', ntag, eraseKey a nl, rfl, gn, fieldsV_eraseKey snl, by simp [lookup_eraseKey], rest'⟩
    · constructor
      · rintro ⟨N', mN', hN'⟩
        rcases List.mem_cons.mp mN' with rfl | mN'
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (sem w).mp (nsem_lit.mp hN')⟩
        · obtain ⟨p, mp, hp⟩ := (sP w).mp ⟨N', mN', hN'⟩
          exact ⟨p, List.mem_append_left _ mp, hp⟩
      · rintro ⟨p, mp, hp⟩
        rcases List.mem_append.mp mp with mp | mp
        · obtain ⟨N', mN', hN'⟩ := (sP w).mpr ⟨p, mp, hp⟩
          exact ⟨N', List.mem_cons_of_mem _ mN', hN'⟩
        · rw [List.mem_singleton] at mp; subst mp
          exact ⟨_, List.mem_cons_self, nsem_lit.mpr ((sem w).mpr hp)⟩

theorem eraseK_setK (a : String) (o : Option V) (w : MW V) : eraseK a (setK a o w) = eraseK a w := by
  funext k; by_cases h : k = .atom a <;> simp [eraseK, setK, h]

theorem eraseK_of_none {a : String} {u : MW V} (h : u (.atom a) = none) : eraseK a u = u := by
  funext k; by_cases hk : k = .atom a
  · subst hk; simp [eraseK, h]
  · simp [eraseK, hk]

/-- Values at a key of the maps of a line. -/
def LongM (den : Term → V → Prop) (L : Term) (a : String) (o : Option V) : Prop :=
  ∃ w, InMLine den L w ∧ w (.atom a) = o

/-- The field and rest of a negated pair. -/
def pairField : Term → Term
  | .tuple ⟨[f, _]⟩ => f
  | _ => .nil

def pairRest : Term → Term × List (Term × Term)
  | .tuple ⟨[_, .tuple ⟨[_, tag, fs]⟩]⟩ => (tag, domFields fs)
  | _ => (.atom "open", [])

/-- A value at a key with a rest outside the negated pairs is the value at the key of a map of the line. -/
theorem long_of_rest (ef : EF nd E V den tl K) (a : String) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {P : List Term} (hP : ∀ p ∈ P, MPairOk E p ∧ RestOk E den a p)
    (sP : ∀ w, (∃ N ∈ negs, NSem den N w) ↔ ∃ p ∈ P, MPairIn E den p (w (.atom a)) (eraseK a w)) {o : Option V}
    (ho : FieldSem den (fieldAt tag l a) o) {w' : MW V} (hw' : MSem den tag (eraseKey a l) w')
    (out : ∀ p ∈ P, ¬MPairIn E den p o w') :
    LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o := by
  classical
  let Ns := (P.filter fun p => decide (FieldSem den (pairField p) o)).map pairRest
  have hN : ∀ N ∈ Ns, mapLookup N.2 (.atom a) = none ∧ ∃ p ∈ P, FieldSem den (pairField p) o ∧
      ∀ w, MSem den N.1 N.2 w → MPairIn E den p o w := by
    intro N mN
    simp only [Ns, List.mem_map, List.mem_filter, decide_eq_true_eq] at mN
    obtain ⟨p, ⟨mp, hf⟩, rfl⟩ := mN
    obtain ⟨-, f, k, ntag, nl, rfl, -, -, na, rest⟩ := hP p mp
    simp only [pairRest, pairField, domFields_fieldsTerm] at hf ⊢
    exact ⟨na, _, mp, hf, fun w hw => mpairIn_iff.mpr ⟨hf, (rest w).mpr hw⟩⟩
  obtain ⟨u, ua, hu, hn⟩ := aless a (by rw [lookup_eraseKey]; simp) Ns (fun N mN => (hN N mN).1) hw'
    (fun N mN hN' => by
      obtain ⟨-, p, mp, -, inc⟩ := hN N mN
      exact out p mp (inc w' hN'))
  refine ⟨setK a o u, inMLine_iff.mpr ⟨(msem_at ef g l a _).mpr ⟨by simpa [setK] using ho, by
    rw [eraseK_setK, eraseK_of_none ua]; exact hu⟩, fun N mN hN' => ?_⟩, by simp [setK]⟩
  obtain ⟨p, mp, hp⟩ := (sP _).mp ⟨N, mN, hN'⟩
  rw [eraseK_setK, eraseK_of_none ua] at hp
  have hpo : MPairIn E den p o u := by simpa [setK] using hp
  obtain ⟨-, f, k, ntag, nl, rfl, -, -, -, rest⟩ := hP p mp
  obtain ⟨hf, hr⟩ := mpairIn_iff.mp hpo
  refine hn (ntag, nl) ?_ ((rest u).mp hr)
  simp only [Ns, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨_, ⟨mp, by simpa [pairField] using hf⟩, by simp [pairRest, domFields_fieldsTerm]⟩

/-- One step of `map_dnf_fetch_static/2`: the field accumulated so far, united with the values at the key of the maps
of a non-empty line. -/
theorem mline_step (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) (a : String) {L : Term} (hL : MLine E L)
    (ne : ∃ w, InMLine den L w) {acc : Term} (ha : FieldValue E acc) :
    ∃ acc', (D (n + 3)).pure (.function "Elixir.Module.Types.Descr" "-map_dnf_fetch_static/2-fun-0-" 2 #[.atom a])
        #[L, acc] = .ok acc' ∧ FieldValue E acc' ∧ ∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den L a o := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨w₀, hw₀⟩ := ne
  obtain ⟨hm₀, hn₀⟩ := inMLine_iff.mp hw₀
  obtain ⟨k, run, ⟨f, b, ef', hf, hb⟩, rest, sem⟩ := pop_pair (den := den) ef g sl a
  simp only [Term.tuple.injEq] at ef'
  obtain ⟨rfl, rfl, -⟩ := ef'
  have split₀ := (msem_at ef g l a w₀).mp hm₀
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_dnf_fetch_static/2-fun-0-/2».pure]
  by_cases nn : negs = []
  · subst nn
    obtain ⟨t₁, o₁, e₁, h₁⟩ := hf
    obtain ⟨t₂, o₂, e₂, h₂⟩ := ha
    obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef (m := n + 2) (by omega) e₁ e₂ h₁ h₂ []
    refine ⟨.tuple #[c, boolAtom (o₁ || o₂)], ?_, ⟨c, _, rfl, hc⟩, fun o => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_dnf_fetch_static/2-fun-0-/3»,
        Elixir.Module.Types.Descr.«map_split_key_line/5», run, rc]
    · rw [sc, or_comm]
      refine or_congr Iff.rfl ⟨fun ho => long_of_rest ef a g (P := []) (by simp) (fun w => by simp) ho split₀.2
        (by simp), ?_⟩
      rintro ⟨w, hw, rfl⟩
      exact ((msem_at ef g l a w).mp (inMLine_iff.mp hw).1).1
  · have nnil : Term.list negs ≠ .nil := by cases negs <;> simp_all [Term.list]
    obtain ⟨r, rr, ⟨rfl, N, mN, hN⟩ | ⟨P, rfl, hP, sP⟩⟩ := msplit_negs (den := den) ef a negs lits []
    · refine ⟨acc, ?_, ha, fun o => ⟨fun h => Or.inl h, fun h => h.elim id fun ⟨w, hw, _⟩ =>
        absurd (hN w) ((inMLine_iff.mp hw).2 N mN)⟩⟩
      simp only [Elixir.Module.Types.Descr.«-map_dnf_fetch_static/2-fun-0-/3»]
      rw [Elixir.Module.Types.Descr.«map_split_key_line/5».eq_def]
      split
      · exact absurd ‹_› nnil
      · simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr]
    simp only [List.append_nil] at rr
    have restNe : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
      ⟨_, (rest _).mpr split₀.2⟩
    obtain ⟨s, acc', rk, hs₁, hs₂, hacc, sacc⟩ := mproj_value ef hn P (fun p mp => (hP p mp).1) hf hb restNe ha
    refine ⟨acc', ?_, hacc, fun o => ?_⟩
    · simp only [Elixir.Module.Types.Descr.«-map_dnf_fetch_static/2-fun-0-/3»]
      rw [Elixir.Module.Types.Descr.«map_split_key_line/5».eq_def]
      split
      · exact absurd ‹_› nnil
      · cases s
        · obtain ⟨Q, rQ, rf⟩ := hs₂ rfl
          cases P with
          | nil => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, rQ, rf,
              Lynx.Term.isMember, boolAtom, Term.list]
          | cons p P => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, rQ, rf,
              Lynx.Term.isMember, boolAtom, Term.list]
        · cases P with
          | nil => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, hs₁ rfl,
              Lynx.Term.isMember, boolAtom, Term.list]
          | cons p P => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, hs₁ rfl,
              Lynx.Term.isMember, boolAtom, Term.list]
    · rw [sacc]
      refine or_congr Iff.rfl ⟨fun ⟨w', hf', hr', out⟩ => long_of_rest ef a g hP sP hf' ((rest w').mp hr') out, ?_⟩
      rintro ⟨w, hw, rfl⟩
      obtain ⟨hmw, hnw⟩ := inMLine_iff.mp hw
      obtain ⟨hfw, hrw⟩ := (msem_at ef g l a w).mp hmw
      exact ⟨eraseK a w, hfw, (rest _).mpr hrw, fun p mp hp => by
        obtain ⟨N, mN, hN⟩ := (sP w).mpr ⟨p, mp, hp⟩
        exact hnw N mN hN⟩

theorem none_field (ef : EF nd E V den tl K) : FieldValue E (.tuple #[.map [], .atom "false"]) ∧
    ∀ o, ¬FieldSem den (.tuple #[.map [], .atom "false"]) o := by
  refine ⟨⟨_, Bool.false, rfl, ef.none⟩, fun o h => ?_⟩
  rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk] at h
  rcases h with ⟨-, h⟩ | ⟨x, -, hx⟩
  · cases h
  · exact ef.den_none x hx

/-- `map_dnf_fetch_static/2` unites the values at a key of the maps of non-empty lines. -/
theorem mdnf_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) (a : String) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ F, Elixir.Module.Types.Descr.«map_dnf_fetch_static/2» (D (n + 3)) (Term.list lines) (.atom a) = .ok F ∧
      FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨F, ⟨hF, sF⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-map_dnf_fetch_static/2-fun-0-"
    #[.atom a] (fun pre acc => FieldValue E acc ∧ ∀ o, FieldSem den acc o ↔ ∃ L ∈ pre, LongM den L a o) lines
    (fun pre L acc mL ⟨ha, sa⟩ => by
      obtain ⟨acc', run, hacc, sacc⟩ := mline_step ef hn a (hl L mL).1 (hl L mL).2 ha
      refine ⟨acc', ⟨hacc, fun o => ?_⟩, run⟩
      rw [sacc, sa]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨L', mL', h⟩ | h)
        · exact ⟨L', Or.inl mL', h⟩
        · exact ⟨L, Or.inr rfl, h⟩
      · rintro ⟨L', mL' | rfl, h⟩
        · exact Or.inl ⟨L', mL', h⟩
        · exact Or.inr h)
    _ ⟨(none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o]⟩
  exact ⟨F, by simpa [Elixir.Module.Types.Descr.«map_dnf_fetch_static/2»] using run, hF, sF⟩

theorem mfield_three {x a b c : Term} (fx : MField E x) (h : x = .tuple ⟨[a, b, c]⟩) :
    ∃ (k : Int) (tag : Term) (l : List (Term × Term)), x = .tuple #[.integer k, tag, fieldsTerm l] ∧ TagV E tag ∧
      FieldsV E l := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, .atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩
  rcases wx.shape with rfl | rfl | ⟨k, y, z, rfl⟩ | ⟨h', lit, c', u, d, rfl⟩
  · cases h
  · cases h
  · obtain ⟨⟨k', tag, l, e, g, sl⟩, -⟩ := Bdd.leaf_iff.mp wx
    exact ⟨k', tag, l, e, g, sl⟩
  · simp at h

/-- A non-empty map literal holds maps with any value of its field at a key. -/
theorem lit_values (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (a : String)
    {w₀ : MW V} (h₀ : MSem den tag l w₀) (o : Option V) :
    FieldSem den (fieldAt tag l a) o ↔ ∃ w, MSem den tag l w ∧ w (.atom a) = o := by
  constructor
  · intro ho
    refine ⟨setK a o w₀, (msem_at ef g l a _).mpr ⟨by simpa [setK] using ho, ?_⟩, by simp [setK]⟩
    rw [eraseK_setK]; exact ((msem_at ef g l a w₀).mp h₀).2
  · rintro ⟨w, hw, rfl⟩
    exact ((msem_at ef g l a w).mp hw).1

/-- `map_fetch_key_static/3` on a map field: `:badmap` when it is empty, otherwise the field of the values at a key of
its maps. -/
theorem mstatic_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (a : String) :
    ∃ res, Elixir.Module.Types.Descr.«map_fetch_key_static/3» (D (n + 3)) (.map X) (.atom a) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (FieldValue E res ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∀ o, FieldSem den res o ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = o)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 3)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 3) (by omega)
    cases e
    · -- Not empty: a map of the literal.
      have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ (m := n + 3) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      refine ⟨fieldAt tag l a, ?_, Or.inr ⟨fieldAt_ok ef g sl a, ⟨w₀, (sem w₀).mpr h₀⟩, fun o => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        have ff := find_val (E := E) a sl
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom,
          Elixir.Module.Types.Descr.«map_fetch_field/3», ff, fieldAt]
        cases h : mapLookup l (.atom a) <;> simp [key_tag_field g]
      · rw [lit_values ef g a h₀]
        exact ⟨fun ⟨w, hw, e⟩ => ⟨w, (sem w).mpr hw, e⟩, fun ⟨w, hw, e⟩ => ⟨w, (sem w).mp hw, e⟩⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ (m := n + 3) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ rfl (m := n + 3) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Lynx.Term.isMember, Term.list]
        · simp [getMapKeys_single, hb, rl, Lynx.Term.isMember, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Lynx.Term.isMember, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a (L :: rest) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨F, ?_, Or.inr ⟨hF, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, fun o => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, rF, Term.list]
        · simp [getMapKeys_single, hb, rl, rF, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, rF, Term.list]
      · rw [sF]
        constructor
        · rintro ⟨L', mL', w, hw, rfl⟩
          exact ⟨w, (inB w).mpr ⟨L', mL', hw⟩, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          obtain ⟨L', mL', hL'⟩ := (inB w).mp hw
          exact ⟨L', mL', w, hL', rfl⟩

end

end Elixir.STTDescrProofsTest.Nest
