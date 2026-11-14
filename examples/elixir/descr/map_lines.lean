namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Lines of map BDDs: a tag, fields, and negated literals. -/
def MLine (E : Term → Prop) (L : Term) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    TagV E tag ∧ FieldsV E l ∧ ∀ t ∈ negs, MapLitV E t

/-- Maps of values in a line. -/
def InMLine (den : Term → V → Prop) (L : Term) (w : MW V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    MSem den tag l w ∧ ∀ N ∈ negs, ¬NSem den N w

theorem inMLine_iff {tag : Term} {l : List (Term × Term)} {negs : List Term} {w : MW V} :
    InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w ↔ MSem den tag l w ∧ ∀ N ∈ negs, ¬NSem den N w := by
  constructor
  · rintro ⟨tag', l', negs', e, h, hn⟩
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    rw [e₁, fieldsTerm_inj e₂, list_inj e₃]
    exact ⟨h, hn⟩
  · intro h; exact ⟨tag, l, negs, rfl, h⟩

/-- `map_bdd_to_dnf/5` lists the lines of a map BDD. -/
theorem dnf_map (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (okT : ∀ t, ok t → MapLitV E t) :
    ∀ (acc : List Term) (pos : Term) (negs : List Term), MapPosV E pos → (∀ t ∈ negs, MapLitV E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list acc) pos (Term.list negs) r (.map S) =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, MLine E L) ∧
        ∀ v, (∃ L ∈ lines, InMLine den L v) ↔
          (InPosM den pos v ∧ (∀ N ∈ negs, ¬NSem den N v) ∧ eval (valM E den v) r = Bool.true) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t) →
    ∀ (acc : List Term) (pos : Term) (negs : List Term), MapPosV E pos → (∀ t ∈ negs, MapLitV E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list acc) pos (Term.list negs) r (.map S) =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, MLine E L) ∧
        ∀ v, (∃ L ∈ lines, InMLine den L v) ↔
          (InPosM den pos v ∧ (∀ N ∈ negs, ¬NSem den N v) ∧ eval (valM E den v) r = Bool.true))
    ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ acc pos negs hp lits
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    refine ⟨[.tuple #[tag, fieldsTerm l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp [inMLine_iff, inPosM_iff]
  · intro ok _ acc pos negs _ _
    refine ⟨[], ?_, by simp, fun v => by simp⟩
    rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp
  · intro ok k x y okl okLit acc pos negs hp lits
    have hl := okLit _ okl
    rcases inter_val ops dops sem hm hS hp hl with ⟨empty, none⟩ | ⟨pos', run, hp', sem'⟩
    · refine ⟨[], ?_, by simp, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [empty]
      · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and, eval_leaf]
        intro hv _ e
        exact none v hv ((valM_iff ops dops sem hl).mp e)
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    refine ⟨[.tuple #[tag, fieldsTerm l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [run, Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp only [List.mem_singleton, exists_eq_left, inMLine_iff, eval_leaf, valM_iff ops dops sem hl]
      rw [← inPosM_iff, sem' v]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc pos negs hp lits
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t := fun t ht => okLit t ht.1
    obtain ⟨Lu, ru, tu, su⟩ := iu okLit' acc pos negs hp lits
    have lits' : ∀ t ∈ lit :: negs, MapLitV E t := fun t mt => by
      rcases List.mem_cons.mp mt with rfl | mt
      · exact hl
      · exact lits t mt
    obtain ⟨Lc, runC, tc, sc⟩ : ∃ Lc,
        ((Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) = .ok (.atom "empty") ∧ Lc = []) ∨
          ∃ tag2 l2, Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) =
              .ok (.tuple #[tag2, fieldsTerm l2]) ∧
            Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list (Lu ++ acc)) (.tuple #[tag2, fieldsTerm l2])
              (Term.list negs) c (.map S) = .ok (Term.list (Lc ++ (Lu ++ acc)))) ∧ (∀ L ∈ Lc, MLine E L) ∧
          ∀ v, (∃ L ∈ Lc, InMLine den L v) ↔
            (InPosM den pos v ∧ NSem den lit v ∧ (∀ N ∈ negs, ¬NSem den N v) ∧ eval (valM E den v) c = Bool.true) := by
      rcases inter_val ops dops sem hm hS hp hl with ⟨empty, none⟩ | ⟨pos2, run, hp2, sem2⟩
      · exact ⟨[], Or.inl ⟨empty, rfl⟩, by simp, fun v => by
          simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
          exact fun hv hlit => absurd hlit (none v hv)⟩
      obtain ⟨Lc, rc, tc, sc⟩ := ic okLit' (Lu ++ acc) pos2 negs hp2 lits
      obtain ⟨tag2, l2, rfl, -⟩ := hp2
      refine ⟨Lc, Or.inr ⟨tag2, l2, run, rc⟩, tc, fun v => ?_⟩
      rw [sc v, sem2 v]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    obtain ⟨Ld, rd, td, sd⟩ := idd okLit' (Lc ++ (Lu ++ acc)) pos (lit :: negs) hp lits'
    rw [list_cons] at rd
    refine ⟨Ld ++ Lc ++ Lu, ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]
      obtain ⟨tag, l, rfl, -⟩ := hp
      rcases runC with ⟨e, rfl⟩ | ⟨tag2, l2, e, rc⟩
      · simp only [List.nil_append] at rd
        simp [ru, e, rd]
      · simp [ru, e, rc, rd]
    · intro L mL
      simp only [List.mem_append] at mL
      rcases mL with (mL | mL) | mL
      · exact td L mL
      · exact tc L mL
      · exact tu L mL
    · have split : (∃ L ∈ Ld ++ Lc ++ Lu, InMLine den L v) ↔
          (∃ L ∈ Ld, InMLine den L v) ∨ (∃ L ∈ Lc, InMLine den L v) ∨ (∃ L ∈ Lu, InMLine den L v) := by
        constructor
        · rintro ⟨L, mL, hL⟩
          simp only [List.mem_append] at mL
          rcases mL with (mL | mL) | mL
          · exact Or.inl ⟨L, mL, hL⟩
          · exact Or.inr (Or.inl ⟨L, mL, hL⟩)
          · exact Or.inr (Or.inr ⟨L, mL, hL⟩)
        · rintro (⟨L, mL, hL⟩ | ⟨L, mL, hL⟩ | ⟨L, mL, hL⟩) <;> exact ⟨L, by simp [mL], hL⟩
      rw [split, sd v, sc v, su v, eval_node]
      by_cases hlit : NSem den lit v
      · have e : valM E den v lit = Bool.true := (valM_iff ops dops sem hl).mpr hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inl ⟨a, b, c⟩) (fun c => Or.inr ⟨a, b, c⟩)⟩
      · have e : valM E den v lit = Bool.false := by
          cases h' : valM E den v lit
          · rfl
          · exact absurd ((valM_iff ops dops sem hl).mp h') hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inr ⟨a, b, c⟩) (fun c => Or.inl ⟨a, b, c⟩)⟩

/-- Map lines either hold a map of values or are empty. -/
theorem mline_keep (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {L : Term}
    (hL : MLine E L) : ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) := by
  obtain ⟨tag, l, negs, rfl, gt, sl, lits⟩ := hL
  obtain ⟨b, run⟩ := init_total ops dops [] gt.plain (fun e me => (sl.1 e me).2) (fun t m => (lits t m).plain)
  have sem' : b = Bool.true ↔ ∀ w, MSem den tag l w → CovM den negs w := by
    constructor
    · rintro rfl; exact init_sound ops dops sem (m := K + 1) (by omega) hS gt sl lits (run (K + 1) (by omega))
    · intro h
      have := (run (K + 1) (by omega)).symm.trans (init_val ops dops sem (m := K + 1) (by omega) hS gt sl lits h)
      cases b
      · simp [boolAtom] at this
      · rfl
  refine ⟨!b, fun m acc hm => ?_, ?_⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_bdd_to_dnf_remove_empty/1-fun-0-/2».pure]
    cases b <;> simp [Elixir.Module.Types.Descr.«-map_bdd_to_dnf_remove_empty/1-fun-0-/2»,
      Elixir.Module.Types.Descr.«init_map_line_empty?/3», run n (by omega), Lynx.Term.isMember, boolAtom]
  · rw [Bool.not_eq_true', ← Bool.not_eq_true, sem']
    constructor
    · intro h
      obtain ⟨w, hw⟩ := Classical.not_forall.mp h
      obtain ⟨hm, hc⟩ := Classical.not_imp.mp hw
      exact ⟨w, inMLine_iff.mpr ⟨hm, fun N mN hN => hc ⟨N, mN, hN⟩⟩⟩
    · rintro ⟨w, hw⟩ h
      obtain ⟨hm, hn⟩ := inMLine_iff.mp hw
      obtain ⟨N, mN, hN⟩ := h w hm
      exact hn N mN hN

/-- `map_bdd_to_dnf_remove_empty/1` lists the non-empty lines of a map BDD. -/
theorem dnf_neg_map (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {m : Nat}
    (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (MLit E) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1» (D m) r =
        .ok (Term.list lines) ∧ (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) ∧
      ∀ w, eval (valM E den w) r = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := by
  obtain ⟨all, run, tl, sl⟩ := dnf_map (den := den) ops dops sem (m := m) hm hS wr (fun t h => h.1) []
    (.tuple #[.atom "open", .nil]) [] ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩ (by simp)
  have keeps : ∀ L ∈ all, ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) :=
    fun L mL => mline_keep ops dops sem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc)) ∧ (keep L = Bool.true ↔ ∃ w, InMLine den L w) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact Classical.choose_spec (keeps L mL)
  have fold := foldl_det (K := K + 2) "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all (fun x mx a m hm => (hk x mx).1 m a hm) .nil hm
  have e := foldl_filter keep all []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all.filter keep).reverse, ?_, fun L mL => ?_, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1»
    have run' : Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r (.map []) =
        .ok (Term.list all) := by simpa using run
    simp only [run', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all)) =
        Erlang.lists.«foldl/3» (D m) (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[])
          .nil (Term.list all) from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact ⟨tl L mL.1, (hk L mL.1).2.mp mL.2⟩
  · have hp : InPosM den (.tuple #[.atom "open", .nil]) w := ⟨.atom "open", [], rfl, ⟨fun s => by
      simp [FSem, TagSem, mapLookup], fun k i => by simp [TagSem]⟩⟩
    rw [← (by simpa [hp] using sl w : (∃ L ∈ all, InMLine den L w) ↔ eval (valM E den w) r = Bool.true)]
    constructor
    · rintro ⟨L, mL, hL⟩
      exact ⟨L, by simp [mL, (hk L mL).2.mpr ⟨w, hL⟩], hL⟩
    · rintro ⟨L, mL, hL⟩
      simp only [List.mem_reverse, List.mem_filter] at mL
      exact ⟨L, mL.1, hL⟩

end

end Elixir.STTDescrProofsTest.Nest
