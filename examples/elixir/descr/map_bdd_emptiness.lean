namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-! Map BDD emptiness on value maps. -/

theorem bare_ifun (ops : ElemOk E K) (_dops : ElemDiff E K) (esem : ElemSem E K V den Safe) : IFun E den (K + 1) bareIntersection := by
  intro m hm a b ha hb
  obtain ⟨c, hc, run⟩ := ops.inter ha hb
  refine ⟨c, hc, esem.inter ha hb (Nat.le_refl K) (run K (Nat.le_refl K)), ?_⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
  rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
  exact run n (by omega)

/-- Fields that compare equal allow the same values. -/
theorem fields_compare (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) : ∀ {l l' : List (Term × Term)}, FieldsV E l → FieldsV E l' →
    compare (fuel (fieldsTerm l) (fieldsTerm l')) (fieldsTerm l) (fieldsTerm l') = .eq → ∀ (tag : Term) s o, FSem den tag l s o ↔ FSem den tag l' s o
  | [], [], _, _, _, _, _, _ => Iff.rfl
  | [], _ :: _, _, _, e, _, _, _ => by simp [fieldsTerm, Term.list] at e
  | _ :: _, [], _, _, e, _, _, _ => by simp [fieldsTerm, Term.list] at e
  | (k, f) :: l, (k', f') :: l', h, h', e, tag, s, o => by
    simp only [fieldsTerm_cons, compare_cons, Ordering.then_eq_eq] at e
    obtain ⟨e₁, e₂⟩ := e
    obtain ⟨a, rfl⟩ := (h.1 _ List.mem_cons_self).1
    obtain ⟨a', rfl⟩ := (h'.1 _ List.mem_cons_self).1
    obtain ⟨t, o₁, rfl, ht⟩ := (h.1 _ List.mem_cons_self).2
    obtain ⟨t', o₂, rfl, ht'⟩ := (h'.1 _ List.mem_cons_self).2
    simp [compare_tuple, List.compareLex_cons_cons] at e₁
    obtain ⟨rfl, ⟨et, eo, -⟩, -⟩ := e₁
    have oo : o₁ = o₂ := by
      cases o₁ <;> cases o₂ <;> simp_all [boolAtom] <;> simp [Term.compare_step, Compare.compareStep] at eo
    subst oo
    have ih := fields_compare ops dops esem (fieldsV_tail h) (fieldsV_tail h') e₂ tag s o
    by_cases as : a = s
    · subst as
      rw [fsem_cons_self, fsem_cons_self, fieldSem_mk, fieldSem_mk]
      have d : ∀ x, den t x ↔ den t' x := fun x =>
        ⟨esem.resp ht' ht (Lynx.Term.compare_eq_symm et), esem.resp ht ht' et⟩
      simp [d]
    · rw [fsem_cons_ne as, fsem_cons_ne as]
      exact ih

/-- Domains that compare equal have the same kinds, with types that compare equal. -/
theorem doms_compare : ∀ {dl dl' : List (Term × Term)}, DomsV E dl → DomsV E dl' →
    compare (fuel (fieldsTerm dl) (fieldsTerm dl')) (fieldsTerm dl) (fieldsTerm dl') = .eq → ∀ s : String,
      (mapLookup dl (.atom s) = Option.none ∧ mapLookup dl' (.atom s) = Option.none) ∨
      ∃ T T', mapLookup dl (.atom s) = some T ∧ mapLookup dl' (.atom s) = some T' ∧ compare (fuel T T') T T' = .eq
  | [], [], _, _, _, s => Or.inl ⟨by simp [mapLookup], by simp [mapLookup]⟩
  | [], _ :: _, _, _, e, _ => by simp [fieldsTerm, Term.list] at e
  | _ :: _, [], _, _, e, _ => by simp [fieldsTerm, Term.list] at e
  | (k, T) :: l, (k', T') :: l', h, h', e, s => by
    simp only [fieldsTerm_cons, compare_cons, Ordering.then_eq_eq] at e
    obtain ⟨e₁, e₂⟩ := e
    obtain ⟨⟨a, rfl, -⟩, -⟩ := h.1 _ List.mem_cons_self
    obtain ⟨⟨a', rfl, -⟩, -⟩ := h'.1 _ List.mem_cons_self
    have t : DomsV E l := ⟨fun e me => h.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp h.2).2⟩
    have t' : DomsV E l' := ⟨fun e me => h'.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp h'.2).2⟩
    simp [compare_tuple, List.compareLex_cons_cons] at e₁
    obtain ⟨rfl, et, -⟩ := e₁
    by_cases as : a = s
    · subst as
      exact Or.inr ⟨T, T', by simp [lookup_cons_atom], by simp [lookup_cons_atom], et⟩
    · rw [lookup_cons_atom, ite_eq_right as, lookup_cons_atom, ite_eq_right as]
      exact doms_compare t t' e₂ s

/-- Tags that compare equal allow the same values. -/
theorem tagSem_compare (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {tag tag' : Term}
    (g : TagV E tag) (g' : TagV E tag') (e : compare (fuel tag tag') tag tag' = .eq) (kind : String) (o : Option V) :
    TagSem den tag kind o ↔ TagSem den tag' kind o := by
  have hnone := (sem_none ops dops esem).2
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · rw [(compare_eq_atom _ _).mp (Lynx.Term.compare_eq_symm e)]
  · rw [(compare_eq_atom _ _).mp (Lynx.Term.compare_eq_symm e)]
  · rcases g' with rfl | rfl | ⟨dl', rfl, dv'⟩
    · exact absurd ((compare_eq_atom _ _).mp e) (fieldsTerm_ne_atom _ _)
    · exact absurd ((compare_eq_atom _ _).mp e) (fieldsTerm_ne_atom _ _)
    · rw [tagSem_dom_iff hnone, tagSem_dom_iff hnone]
      rcases doms_compare dv dv' e kind with ⟨n, n'⟩ | ⟨T, T', hT, hT', et⟩
      · simp [n, n']
      · have ET : E T := by obtain ⟨x, mx, -, rfl⟩ := lookup_mem_key hT; exact (dv.1 x mx).2
        have ET' : E T' := by obtain ⟨x, mx, -, rfl⟩ := lookup_mem_key hT'; exact (dv'.1 x mx).2
        have d : ∀ v, den T v ↔ den T' v := fun v =>
          ⟨esem.resp ET' ET (Lynx.Term.compare_eq_symm et), esem.resp ET ET' et⟩
        simp [hT, hT', d]

/-- Map lines: a tag and fields of value maps. -/
def MapPosV (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)), p = .tuple #[tag, fieldsTerm l] ∧ TagV E tag ∧ FieldsV E l

def InPosM (den : Term → V → Prop) (p : Term) (w : (MW V)) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)), p = .tuple #[tag, fieldsTerm l] ∧ MSem den tag l w

theorem inPosM_iff {tag : Term} {l : List (Term × Term)} {w : (MW V)} :
    InPosM den (.tuple #[tag, fieldsTerm l]) w ↔ MSem den tag l w := by
  constructor
  · rintro ⟨tag', l', e, h⟩
    simp only [Term.tuple.injEq] at e
    have e₀ := congrArg (fun a : Array Term => a[0]?) e
    have e₁ := congrArg (fun a : Array Term => a[1]?) e
    simp at e₀ e₁
    rw [e₀, fieldsTerm_inj e₁]
    exact h
  · intro h; exact ⟨tag, l, rfl, h⟩

open Classical in
/-- The valuation of map literals that a map of values induces, up to comparison. -/
noncomputable def valM (E : Term → Prop) (den : Term → V → Prop) (w : (MW V)) (t : Term) : Bool := decide (∃ t', compare (fuel t t') t t' = .eq ∧ MapLitV E t' ∧ NSem den t' w)

theorem valM_resp (w : (MW V)) : Resp (valM E den w) := by
  intro a b h
  simp only [valM]
  congr 1
  apply propext
  constructor
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans h e, rest⟩

theorem valM_true {w : (MW V)} {t : Term} (ht : MapLitV E t) (h : NSem den t w) : valM E den w t = Bool.true := by
  simp only [valM, decide_eq_true_eq]
  exact ⟨t, compare_self t, ht, h⟩

theorem valM_lit (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {w : (MW V)} {t : Term} (ht : MapLitV E t) (h : valM E den w t = Bool.true) : NSem den t w := by
  simp only [valM, decide_eq_true_eq] at h
  obtain ⟨t', e, ⟨k', tag', l', rfl, g', sl'⟩, hn⟩ := h
  obtain ⟨k, tag, l, rfl, g, sl⟩ := ht
  simp only [compare_tuple, Array.size, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
    Ordering.eq_then, List.compareLex_cons_cons, Ordering.then_eq_eq] at e
  obtain ⟨-, et, el, -⟩ := e
  rw [nsem_lit] at hn ⊢
  have ts := tagSem_compare ops dops esem g g' et
  refine ⟨fun s => ?_, fun k i => (ts _ _).mpr (hn.doms k i)⟩
  have := (fields_compare ops dops esem sl sl' el tag' s (w (.atom s))).mpr (hn s)
  unfold FSem at this ⊢
  cases h : mapLookup l (.atom s) <;> simp only [h] at this ⊢
  · exact (ts _ _).mpr this
  · exact this

theorem valM_iff (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {w : (MW V)} {t : Term} (ht : MapLitV E t) : valM E den w t = Bool.true ↔ NSem den t w :=
  ⟨valM_lit ops dops esem ht, valM_true ht⟩

/-- `map_line_intersection/3` on value maps. -/
theorem inter_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m) {S : List (Term × Term)} (hS : Safe S) {pos lit : Term}
    (hp : MapPosV E pos) (hl : MapLitV E lit) :
    (Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) = .ok (.atom "empty") ∧
      ∀ w, InPosM den pos w → ¬NSem den lit w) ∨
    ∃ pos', Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) = .ok pos' ∧ MapPosV E pos' ∧
      ∀ w, InPosM den pos' w ↔ InPosM den pos w ∧ NSem den lit w := by
  obtain ⟨tag, l, rfl, gt, sl⟩ := hp
  obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := hl
  rcases literal_val ops dops esem (Kf := K + 1) (show K + 1 + 1 ≤ m by omega) (by omega) (bare_ifun ops dops esem) hS gt gn sl snl with
    ⟨tR, l', run, gR, sl', sem⟩ | ⟨disj, run⟩
  · right
    refine ⟨_, ?_, ⟨tR, l', rfl, gR, sl'⟩, fun w => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
      simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
      simp [run]
    · rw [inPosM_iff, inPosM_iff, nsem_lit]; exact sem w
  · left
    refine ⟨?_, fun w hw hn => disj w ⟨inPosM_iff.mp hw, nsem_lit.mp hn⟩⟩
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason]

/-- No map of values along the path, outside the negated literals, satisfies the BDD. -/
def ValUnsatM (E : Term → Prop) (den : Term → V → Prop) (pos : Term) (negs : List Term) (r : Term) : Prop :=
  ∀ w, InPosM den pos w → (∀ N ∈ negs, ¬NSem den N w) → eval (valM E den w) r = Bool.false

theorem covM_of_unsat {pos : Term} {negs : List Term} {w : (MW V)}
    (h : InPosM den pos w → (∀ N ∈ negs, ¬NSem den N w) → False) (hw : InPosM den pos w) : CovM den negs w :=
  Classical.byContradiction fun none => h hw fun N mN hN => none ⟨N, mN, hN⟩

theorem map_bdd_val (ops : ElemOk E K) (dops : ElemDiff E K) (esem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m) (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term}
    (wr : Bdd ok r) :
    (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos → (∀ t ∈ negs, MapLitV E t) → ValUnsatM E den pos negs r →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t) → ∀ pos negs, MapPosV E pos →
    (∀ t ∈ negs, MapLitV E t) → ValUnsatM E den pos negs r →
    Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits g
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    simp only
    exact init_val ops dops esem (by omega) hS gt sl lits fun w hw =>
      covM_of_unsat (fun hw' nn => by have := g w hw' nn; simp at this) (inPosM_iff.mpr hw)
  · intro ok _ pos negs _ _ _
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    split <;> simp_all
  · intro ok k x y okl okLit pos negs hp lits g
    have hl := okLit _ okl
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    rcases inter_val ops dops esem hm hS hp hl with ⟨empty, -⟩ | ⟨pos', run, hp', sem'⟩
    · simp [empty]
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp'
    simp [run]
    refine init_val ops dops esem (by omega) hS gt sl lits fun w hw => ?_
    obtain ⟨hpos, hlit⟩ := (sem' w).mp (inPosM_iff.mpr hw)
    refine covM_of_unsat (fun hw' nn => ?_) hpos
    have := g w hw' nn
    rw [eval_leaf, valM_true hl hlit] at this
    cases this
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits g
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t := fun t ht => okLit t ht.1
    have dPart : Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list (lit :: negs)) d (.map S) =
        .ok (.atom "true") := by
      refine idd okLit' pos (lit :: negs) hp (fun t m => ?_) fun w hw nn => ?_
      · rcases List.mem_cons.mp m with rfl | m
        · exact hl
        · exact lits t m
      have nl : valM E den w lit = Bool.false := by
        cases e : valM E den w lit
        · rfl
        · exact absurd (valM_lit ops dops esem hl e) (nn lit List.mem_cons_self)
      have := g w hw fun N mN => nn N (List.mem_cons_of_mem _ mN)
      simp only [eval_node, nl] at this
      simp at this
      exact this.2
    have uPart := iu okLit' pos negs hp lits fun w hw nn => by
      have := g w hw nn
      simp only [eval_node] at this
      cases hu' : eval (valM E den w) u
      · rfl
      · simp [hu'] at this
    rw [list_cons] at dPart
    obtain ⟨tag, l, rfl, gt, sl⟩ := hp
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    rcases inter_val ops dops esem hm hS ⟨tag, l, rfl, gt, sl⟩ hl with ⟨empty, -⟩ | ⟨pos2, run, hp2, sem2⟩
    · simp [empty, dPart, uPart, Lynx.Except.andAlso]
    have cRes := ic okLit' pos2 negs hp2 lits fun w hw nn => by
      obtain ⟨hpos, hlit⟩ := (sem2 w).mp hw
      have := g w hpos nn
      simp only [eval_node, valM_true hl hlit] at this
      simp at this
      exact this.1
    obtain ⟨tag2, l2, rfl, -⟩ := hp2
    simp [run, dPart, uPart, Lynx.Except.andAlso, cRes]

end Elixir.STTDescrProofsTest.Nest
