namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-- Element types denote sets of values `V`: they intersect and subtract as sets, and are empty exactly when
they denote nothing, at every call depth from `K`. -/
structure ElemSem (E : Term → Prop) (K : Nat) (V : Type) (den : Term → V → Prop) (Safe : List (Term × Term) → Prop) :
    Prop where
  term : ∀ v, den (.atom "term") v
  inter : ∀ {a b c : Term} {m : Nat}, E a → E b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c → ∀ v, den c v ↔ den a v ∧ den b v
  diff : ∀ {a b c : Term} {m : Nat}, E a → E b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c → ∀ v, den c v ↔ den a v ∧ ¬den b v
  empty : ∀ {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool}, E a → Safe S → K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b) → (b = Bool.true ↔ ∀ v, ¬den a v)
  inhabited : Nonempty V
  resp : ∀ {e e' : Term} {v : V}, E e → E e' → compare (fuel e e') e e' = .eq → den e' v → den e v

variable {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Tuples of values in the elements of a tuple literal: of the same size when closed, otherwise at least as large. -/
def InT (den : Term → V → Prop) (closed : Bool) : List Term → List V → Prop
  | [], [] => True
  | [], _ :: _ => closed = Bool.false
  | _ :: _, [] => False
  | e :: es, x :: xs => den e x ∧ InT den closed es xs

/-- Tuples of values in a tuple literal. -/
def LitSem (den : Term → V → Prop) (lit : Term) (v : List V) : Prop :=
  ∃ (k : Int) (tag : String) (l : List Term), lit = .tuple #[.integer k, .atom tag, Term.list l] ∧
    InT den (tag == "closed") l v

theorem InT.length_le {c : Bool} : ∀ {l : List Term} {v : List V}, InT den c l v → l.length ≤ v.length
  | [], _, _ => by simp
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simpa using InT.length_le h.2

theorem InT.closed_length : ∀ {l : List Term} {v : List V}, InT den Bool.true l v → v.length = l.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [InT] at h
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simpa using InT.closed_length h.2

/-- Splitting the values of a tuple at a prefix of its elements. -/
theorem InT.append {c : Bool} : ∀ (l₁ : List Term) {l₂ : List Term} {v : List V},
    InT den c (l₁ ++ l₂) v ↔ ∃ v₁ v₂, v = v₁ ++ v₂ ∧ InT den Bool.true l₁ v₁ ∧ InT den c l₂ v₂
  | [], l₂, v => ⟨fun h => ⟨[], v, rfl, trivial, h⟩, fun ⟨v₁, v₂, e, h₁, h₂⟩ => by
      cases v₁ with
      | nil => simpa [e] using h₂
      | cons _ _ => simp [InT] at h₁⟩
  | e :: l₁, l₂, [] => ⟨fun h => h.elim, fun ⟨v₁, v₂, ev, h₁, _⟩ => by
      cases v₁ with
      | nil => exact h₁.elim
      | cons _ _ => simp at ev⟩
  | e :: l₁, l₂, x :: v => by
      have ih := InT.append (c := c) l₁ (l₂ := l₂) (v := v)
      constructor
      · rintro ⟨hx, h⟩
        obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := ih.mp h
        exact ⟨x :: v₁, v₂, rfl, ⟨hx, h₁⟩, h₂⟩
      · rintro ⟨v₁, v₂, ev, h₁, h₂⟩
        cases v₁ with
        | nil => exact h₁.elim
        | cons y v₁ =>
          simp only [List.cons_append, List.cons.injEq] at ev
          obtain ⟨rfl, rfl⟩ := ev
          exact ⟨h₁.1, ih.mpr ⟨v₁, v₂, rfl, h₁.2, h₂⟩⟩

/-- Non-empty element types have values. -/
theorem full_witness (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S) {e : Term} (h : Full E K S e) :
    ∃ x, den e x := by
  have := (sem.empty (b := Bool.false) h.1 hS (Nat.le_refl K) (by simpa using h.2 K (Nat.le_refl K)))
  exact Classical.byContradiction fun none => by
    have := this.mpr (fun v hv => none ⟨v, hv⟩); cases this

/-- Tuples of non-empty element types have values of every size they allow. -/
theorem tuple_witness (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S) :
    ∀ (l : List Term), (∀ e ∈ l, Full E K S e) → ∀ (c : Bool) (extra : Nat), ∃ v : List V, InT den c l v ∧
      v.length = l.length + (if c then 0 else extra)
  | [], _, c, extra => by
    obtain ⟨x⟩ := sem.inhabited
    cases c with
    | true => exact ⟨[], trivial, rfl⟩
    | false =>
      cases extra with
      | zero => exact ⟨[], trivial, rfl⟩
      | succ k => exact ⟨List.replicate (k + 1) x, by simp [List.replicate, InT], by simp⟩
  | e :: l, hl, c, extra => by
    obtain ⟨x, hx⟩ := full_witness sem hS (hl e List.mem_cons_self)
    obtain ⟨v, hv, len⟩ := tuple_witness sem hS l (fun e m => hl e (List.mem_cons_of_mem _ m)) c extra
    exact ⟨x :: v, ⟨hx, hv⟩, by simp [len]; omega⟩

theorem list_inj : ∀ {l l' : List Term}, Term.list l = Term.list l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Term.list] at h
  | _ :: _, [], h => by simp [Term.list] at h
  | x :: l, y :: l', h => by
    simp only [Term.list, Term.cons.injEq] at h
    rw [h.1, list_inj h.2]

theorem InT.mid {c : Bool} (l₁ : List Term) (x : Term) (l₂ : List Term) {v : List V} :
    InT den c (l₁ ++ x :: l₂) v ↔ ∃ v₁ y v₂, v = v₁ ++ y :: v₂ ∧ InT den Bool.true l₁ v₁ ∧ den x y ∧ InT den c l₂ v₂ := by
  rw [InT.append]
  constructor
  · rintro ⟨v₁, w, rfl, h₁, h₂⟩
    cases w with
    | nil => exact h₂.elim
    | cons y v₂ => exact ⟨v₁, y, v₂, rfl, h₁, h₂.1, h₂.2⟩
  · rintro ⟨v₁, y, v₂, rfl, h₁, hx, h₂⟩
    exact ⟨v₁, y :: v₂, rfl, h₁, hx, h₂⟩

theorem InT.replace {c : Bool} {l₁ : List Term} {x x' : Term} {l₂ : List Term} {v : List V}
    (h : InT den c (l₁ ++ x :: l₂) v) (sub : ∀ y, den x y → den x' y) : InT den c (l₁ ++ x' :: l₂) v := by
  obtain ⟨v₁, y, v₂, rfl, h₁, hx, h₂⟩ := (InT.mid l₁ x l₂).mp h
  exact (InT.mid l₁ x' l₂).mpr ⟨v₁, y, v₂, rfl, h₁, sub y hx, h₂⟩

theorem InT.extend : ∀ {l : List Term} {v : List V} (w : List V), InT den Bool.true l v → InT den Bool.false l (v ++ w)
  | [], [], [], _ => trivial
  | [], [], _ :: _, _ => rfl
  | [], _ :: _, _, h => by simp [InT] at h
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, w, h => ⟨h.1, InT.extend w h.2⟩

theorem InT.open_prefix {l₁ l₂ : List Term} {v : List V} (h : InT den Bool.false (l₁ ++ l₂) v) :
    InT den Bool.false l₁ v := by
  obtain ⟨v₁, v₂, rfl, h₁, -⟩ := (InT.append l₁).mp h
  exact InT.extend v₂ h₁

/-- Values of a tuple literal hold, at each position of its elements, a value of that element. -/
theorem lit_at {k : Int} {ntag : String} {pre post : List Term} {nt : Term} {v₁ v₂ : List V} {y : V}
    (h : LitSem den (Term.tuple #[Term.integer k, Term.atom ntag, Term.list (pre ++ nt :: post)]) (v₁ ++ y :: v₂))
    (len : v₁.length = pre.length) : den nt y := by
  obtain ⟨k', tag', l, e, hl⟩ := h
  simp only [Term.tuple.injEq] at e
  have el : Term.list l = Term.list (pre ++ nt :: post) := by
    have := congrArg (fun a : Array Term => a[2]?) e
    simpa using this.symm
  rw [list_inj el] at hl
  obtain ⟨w₁, z, w₂, ew, h₁, hz, -⟩ := (InT.mid pre nt post).mp hl
  have := h₁.closed_length
  obtain ⟨-, e₂⟩ := List.append_inj ew (by omega)
  simp only [List.cons.injEq] at e₂
  rw [e₂.1]
  exact hz

/-- `tuple_elements_empty?/6` finds the remaining values of a line, outside the negated literal, covered by the
remaining negations. -/
theorem elements_complete (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) (c : Bool) (negs : List Term)
    (line : ∀ l : List Term, (∀ e ∈ l, Full E K S e) → (∀ v, InT den c l v → ∃ N ∈ negs, LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "true"))
    (k : Int) (ntag : String) :
    ∀ (nrest pre acc rest : List Term), (∀ e ∈ nrest, E e) → pre.length = acc.length → (∀ e ∈ acc, Full E K S e) →
      (∀ e ∈ rest, Full E K S e) → (c = Bool.true → nrest.length ≤ rest.length) →
      (∀ v, InT den c (acc.reverse ++ rest) v →
        ¬LitSem den (Term.tuple #[Term.integer k, Term.atom ntag, Term.list (pre ++ nrest)]) v → ∃ N ∈ negs, LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_elements_empty?/6» (D m) (Term.list acc) (.atom (if c then "closed" else "open"))
        (Term.list rest) (Term.list nrest) (Term.list negs) (.map S) = .ok (.atom "true") := by
  intro nrest
  induction nrest with
  | nil =>
    intro _ _ _ _ _ _ _ _ _
    rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
    rfl
  | cons nt nl ih =>
    intro pre acc rest hn hpre hacc hrest hlen H
    have hnt := hn nt List.mem_cons_self
    have hnl : ∀ e ∈ nl, E e := fun e m => hn e (List.mem_cons_of_mem _ m)
    -- the next element of the line, `term` past the end of open lines
    obtain ⟨ty, es, hshape, hty, hes, back⟩ : ∃ ty es, ((rest = [] ∧ ty = .atom "term" ∧ es = []) ∨ rest = ty :: es) ∧
        Full E K S ty ∧ (∀ e ∈ es, Full E K S e) ∧
        ∀ v, InT den c (acc.reverse ++ ty :: es) v → InT den c (acc.reverse ++ rest) v := by
      cases rest with
      | nil =>
        have hc : c = Bool.false := by
          cases c
          · rfl
          · have := hlen rfl; simp at this
        subst hc
        exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, full_term ops S, by simp, fun v h => by
          simpa using InT.open_prefix (l₂ := [.atom "term"]) h⟩
      | cons x xs => exact ⟨x, xs, Or.inr rfl, hrest x List.mem_cons_self,
          fun e m => hrest e (List.mem_cons_of_mem _ m), fun v h => h⟩
    have notN : ∀ v₁ y v₂, v₁.length = acc.length → ¬den nt y →
        ¬LitSem den (Term.tuple #[Term.integer k, Term.atom ntag, Term.list (pre ++ nt :: nl)]) (v₁ ++ y :: v₂) :=
      fun v₁ y v₂ len ny h => ny (lit_at h (by omega))
    have allRev : ∀ x, Full E K S x → ∀ e ∈ acc.reverse ++ x :: es, Full E K S e := by
      intro x hx e m
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
      rcases m with m | rfl | m
      · exact hacc e m
      · exact hx
      · exact hes e m
    obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty.1 hnt
    have step := elements_step (D m) acc (.atom (if c then "closed" else "open")) rest nt nl (Term.list negs) (.map S)
      ty es hshape meet (hmeet m hm)
    have dmeet := sem.inter hty.1 hnt hm (hmeet m hm)
    obtain ⟨bm, em⟩ := ops.empty lmeet S
    cases bm
    · have fullMeet : Full E K S meet := ⟨lmeet, fun m' h' => by simpa [boolAtom] using em m' h'⟩
      obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty.1 hnt
      have ddiff := sem.diff hty.1 hnt hm (hdiff m hm)
      obtain ⟨bd, ed⟩ := ops.empty ldiff S
      have pre' : (pre ++ [nt]).length = (ty :: acc).length := by simp [hpre]
      have assoc : pre ++ nt :: nl = (pre ++ [nt]) ++ nl := by simp
      cases bd
      · have fullDiff : Full E K S diff := ⟨ldiff, fun m' h' => by simpa [boolAtom] using ed m' h'⟩
        rw [((step.2 _ (fullMeet.2 m hm) (hdiff m hm)).2 (fullDiff.2 m hm))]
        have l₁ := line _ (allRev diff fullDiff) (fun v hv => by
          obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid _ _ _).mp hv
          have hy' := (ddiff y).mp hy
          refine H _ (back _ ((InT.mid _ _ _).mpr ⟨v₁, y, v₂, rfl, h₁, hy'.1, h₂⟩)) (notN v₁ y v₂ ?_ hy'.2)
          rw [h₁.closed_length]; simp)
        have e₂ := ih (pre ++ [nt]) (meet :: acc) es hnl pre' (fun e m => by
            rcases List.mem_cons.mp m with rfl | m
            · exact fullMeet
            · exact hacc e m) hes (fun hc => by have h := hlen hc; rcases hshape with ⟨rfl, -, rfl⟩ | rfl <;> simp at h ⊢ <;> omega)
          (fun v hv nN => by
            refine H _ (back _ ?_) (by rw [assoc]; exact nN)
            have := hv
            simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
            exact this.replace fun y hy => ((dmeet y).mp hy).1)
        rw [l₁, e₂]
        rfl
      · rw [((step.2 _ (fullMeet.2 m hm) (hdiff m hm)).1 (by simpa [boolAtom] using ed m hm))]
        have sub : ∀ y, den ty y → den nt y := by
          intro y hy
          have none := (sem.empty ldiff hS hm (ed m hm)).mp rfl y
          exact Classical.byContradiction fun ny => none ((ddiff y).mpr ⟨hy, ny⟩)
        exact ih (pre ++ [nt]) (ty :: acc) es hnl pre' (fun e m => by
            rcases List.mem_cons.mp m with rfl | m
            · exact hty
            · exact hacc e m) hes (fun hc => by have h := hlen hc; rcases hshape with ⟨rfl, -, rfl⟩ | rfl <;> simp at h ⊢ <;> omega)
          (fun v hv nN => by
            refine H _ (back _ ?_) (by rw [assoc]; exact nN)
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hv)
    · rw [step.1 (by simpa [boolAtom] using em m hm)]
      have none := (sem.empty lmeet hS hm (em m hm)).mp rfl
      exact line _ (allRev ty hty) fun v hv => by
        obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid _ _ _).mp hv
        refine H _ (back _ hv) (notN v₁ y v₂ ?_ fun ny => none y ((dmeet y).mpr ⟨hy, ny⟩))
        rw [h₁.closed_length]; simp

theorem InT.fill {l : List Term} {j : Nat} {v : List V} (h : InT den Bool.true (l ++ List.replicate j (Term.atom "term")) v) :
    InT den Bool.false l v ∧ v.length = l.length + j := by
  obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := (InT.append l).mp h
  refine ⟨InT.extend v₂ h₁, ?_⟩
  simp [h₁.closed_length, h₂.closed_length]

theorem InT.fill_open {l : List Term} {j : Nat} {v : List V}
    (h : InT den Bool.false (l ++ List.replicate j (Term.atom "term")) v) : InT den Bool.false l v ∧ l.length + j ≤ v.length :=
  ⟨InT.open_prefix h, by have := h.length_le; simpa using this⟩

theorem lit_sem {k : Int} {ntag : String} {nl : List Term} {v : List V}
    (h : LitSem den (.tuple #[.integer k, .atom ntag, Term.list nl]) v) : InT den (ntag == "closed") nl v := by
  obtain ⟨k', tag', l, e, hl⟩ := h
  simp only [Term.tuple.injEq] at e
  have e₁ : Term.atom ntag = Term.atom tag' := by have := congrArg (fun a : Array Term => a[1]?) e; simpa using this
  have e₂ : Term.list nl = Term.list l := by have := congrArg (fun a : Array Term => a[2]?) e; simpa using this
  simp only [Term.atom.injEq] at e₁
  rw [e₁, list_inj e₂]
  exact hl

/-- Tuple lines of non-empty element types are empty when their negations cover their values. -/
theorem line_complete (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, TupleLit E t) → ∀ (c : Bool) (l : List Term), (∀ e ∈ l, Full E K S e) →
      (∀ v, InT den c l v → ∃ N ∈ negs, LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil =>
    intro _ c l hl H
    obtain ⟨v, hv, -⟩ := tuple_witness sem hS l hl c 0
    obtain ⟨N, mN, -⟩ := H v hv
    simp at mN
  | cons N rest ih =>
    intro lits c l hl H
    obtain ⟨k, ntag, nl, rfl, htag, hnl⟩ := lits N List.mem_cons_self
    have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    rw [list_cons]
    by_cases top : ntag = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact line_top _ _ _ k _ (.map S)
    by_cases last : c = Bool.false ∧ ntag = "closed" ∧ rest = []
    · exfalso
      obtain ⟨rfl, rfl, rfl⟩ := last
      obtain ⟨v, hv, len⟩ := tuple_witness sem hS l hl Bool.false (nl.length + 1)
      obtain ⟨N', mN, hN⟩ := H v hv
      simp only [List.mem_singleton] at mN
      subst mN
      have := (lit_sem hN).closed_length
      simp at len; omega
    have notLast : ¬((if c then "closed" else "open") = "open" ∧ ntag = "closed" ∧ rest = []) := by
      rintro ⟨hc, h₁, h₂⟩
      cases c
      · exact last ⟨rfl, h₁, h₂⟩
      · simp at hc
    rw [line_cons (D m) _ l k ntag nl rest (.map S) top notLast]
    have covered : ∀ v, InT den c l v → ¬InT den (ntag == "closed") nl v → ∃ N ∈ rest, LitSem den N v := by
      intro v hv nN
      obtain ⟨N', mN, hN⟩ := H v hv
      rcases List.mem_cons.mp mN with rfl | mN
      · exact absurd (lit_sem hN) nN
      · exact ⟨N', mN, hN⟩
    by_cases skip : ((if c then "closed" else "open") = "closed" ∧ l.length < nl.length) ∨
        (ntag = "closed" ∧ nl.length < l.length)
    · rw [ite_eq_left skip]
      refine ih lits' c l hl fun v hv => covered v hv fun hN => ?_
      have le := hv.length_le
      have le' := hN.length_le
      cases c
      · rcases skip with ⟨h, -⟩ | ⟨hc, lt⟩
        · simp at h
        · subst hc; have := hN.closed_length; omega
      · rcases skip with ⟨-, lt⟩ | ⟨hc, lt⟩
        · have := hv.closed_length; omega
        · subst hc; have := hN.closed_length; omega
    · rw [ite_eq_right skip]
      have noLong : ntag = "closed" → l.length ≤ nl.length := fun hc => by
        have : ¬nl.length < l.length := fun h => skip (Or.inr ⟨hc, h⟩)
        omega
      have elems := elements_complete ops dops sem hm S hS c rest (fun l' hl' H' => ih lits' c l' hl' H') k ntag nl []
        [] l hnl rfl (by simp) hl (fun hc => by
          subst hc
          have : ¬l.length < nl.length := fun h => skip (Or.inl ⟨rfl, h⟩)
          simp; omega)
        (fun v hv nN => covered v (by simpa using hv) fun hN => nN ⟨k, ntag, nl, by simp, hN⟩)
      have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D m) (.integer l.length) (.integer nl.length)
          (.atom (if c then "closed" else "open")) (Term.list l) (.atom ntag) (Term.list rest) (.map S) =
          .ok (.atom "true") := by
        apply arity_true
        cases c
        · right
          refine ⟨sizes_all (D m) l nl.length _ _ (fun i le lt => ?_) l.length (Nat.le_refl _), ?_⟩
          · refine ih lits' Bool.true _ (fun e me => ?_) fun v hv => covered v (InT.fill hv).1 fun hN => ?_
            · simp only [List.mem_append, List.mem_replicate] at me
              rcases me with me | ⟨-, rfl⟩
              · exact hl e me
              · exact full_term ops S
            · have := hN.length_le
              have := (InT.fill hv).2
              omega
          · by_cases o : ntag = "open"
            · exact Or.inl o
            · have hc : ntag = "closed" := by rcases htag with h | h <;> simp_all
              refine Or.inr ⟨by have := noLong hc; omega, ?_⟩
              refine ih lits' Bool.false _ (fun e me => ?_) fun v hv => covered v (InT.fill_open hv).1 fun hN => ?_
              · simp only [List.mem_append, List.mem_replicate] at me
                rcases me with me | ⟨-, rfl⟩
                · exact hl e me
                · exact full_term ops S
              · have := noLong hc
                subst hc
                have := hN.closed_length
                have := (InT.fill_open hv).2
                omega
        · left; rfl
      rw [elems, arity]
      rfl

theorem InT.open_nil (v : List V) : InT den Bool.false [] v := by
  cases v <;> simp [InT]

theorem InT.iff_open {c : Bool} : ∀ {l : List Term} {v : List V},
    InT den c l v ↔ InT den Bool.false l v ∧ (c = Bool.true → v.length = l.length)
  | [], [] => by simp [InT]
  | [], _ :: _ => by cases c <;> simp [InT]
  | _ :: _, [] => by simp [InT]
  | e :: l, x :: v => by
    have ih := InT.iff_open (c := c) (l := l) (v := v)
    simp only [InT, List.length_cons, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨⟨hx, (ih.mp h).1⟩, (ih.mp h).2⟩
    · rintro ⟨⟨hx, h⟩, len⟩; exact ⟨hx, ih.mpr ⟨h, len⟩⟩

/-- Element-wise intersections of the elements of two tuples hold the values of both, past the shorter one too. -/
theorem zip_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) :
    ∀ (l₁ : List Term), (∀ e ∈ l₁, E e) → ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc : List Term,
      ∃ r : List Term, Elixir.Module.Types.Descr.«zip_intersection/4» (D m) (Term.list l₁) (Term.list l₂)
          (Term.list acc) (.function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) =
          .ok (Term.list (acc.reverse ++ r)) ∧ (∀ e ∈ r, E e) ∧ r.length = max l₁.length l₂.length ∧
        ∀ v, InT den Bool.false r v ↔ InT den Bool.false l₁ v ∧ InT den Bool.false l₂ v := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  intro l₁
  induction l₁ with
  | nil =>
    intro _ l₂ h₂ acc
    refine ⟨l₂, ?_, h₂, by simp, fun v => by simp [InT.open_nil]⟩
    unfold Elixir.Module.Types.Descr.«zip_intersection/4»
    exact reverse_list acc l₂
  | cons x xs ih =>
    intro h₁ l₂ h₂ acc
    cases l₂ with
    | nil =>
      refine ⟨x :: xs, ?_, h₁, by simp, fun v => by simp [InT.open_nil]⟩
      unfold Elixir.Module.Types.Descr.«zip_intersection/4»
      exact reverse_list acc (x :: xs)
    | cons y ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      obtain ⟨e, he, run⟩ := ops.inter hx hy
      obtain ⟨r, runr, hr, len, semr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
        (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (e :: acc)
      refine ⟨e :: r, ?_, fun e' me => ?_, by simp [len], fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«zip_intersection/4»
        simp [run n hn]
        simpa using runr
      · rcases List.mem_cons.mp me with rfl | me
        · exact he
        · exact hr e' me
      · have de := sem.inter hx hy hn (run n hn)
        cases v with
        | nil => simp [InT]
        | cons z v =>
          simp only [InT, semr v, de z]
          exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩

/-- The values of a tuple line. -/
def InPos (den : Term → V → Prop) (pos : Term) (v : List V) : Prop :=
  ∃ (tag : String) (l : List Term), pos = .tuple #[.atom tag, Term.list l] ∧ InT den (tag == "closed") l v

theorem inPos_iff {tag : String} {l : List Term} {v : List V} :
    InPos den (.tuple #[.atom tag, Term.list l]) v ↔ InT den (tag == "closed") l v := by
  constructor
  · rintro ⟨tag', l', e, h⟩
    simp only [Term.tuple.injEq] at e
    have e₁ : Term.atom tag = Term.atom tag' := by have := congrArg (fun a : Array Term => a[0]?) e; simpa using this
    have e₂ : Term.list l = Term.list l' := by have := congrArg (fun a : Array Term => a[1]?) e; simpa using this
    simp only [Term.atom.injEq] at e₁
    rw [e₁, list_inj e₂]
    exact h
  · intro h; exact ⟨tag, l, rfl, h⟩

/-- Intersecting a tuple line with a literal keeps the values of both. -/
theorem inter_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {pos lit : Term}
    (hp : TuplePos E pos) (hl : TupleOk E lit) :
    (Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok (.atom "empty") ∧
        ∀ v, InPos den pos v → ¬LitSem den lit v) ∨
      ∃ pos', Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok pos' ∧
        TuplePos E pos' ∧ ∀ v, InPos den pos' v ↔ InPos den pos v ∧ LitSem den lit v := by
  obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
  obtain ⟨⟨k, t₂, l₂, rfl, g₂, e₂⟩, -⟩ := hl
  obtain ⟨v, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  obtain ⟨r, zip, hr, len, semr⟩ := zip_sem ops sem hm l₁ e₁ l₂ e₂ []
  simp only [List.reverse_nil, List.nil_append] at zip
  have litIff : ∀ w, LitSem den (.tuple #[.integer k, .atom t₂, Term.list l₂]) w ↔ InT den (t₂ == "closed") l₂ w :=
    fun w => ⟨lit_sem, fun h => ⟨k, t₂, l₂, rfl, h⟩⟩
  unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
  simp only [length_list, Lynx.Except.ok_bind, hv]
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · left
    refine ⟨by rw [disj.mpr d]; rfl, fun w hw hlw => ?_⟩
    rw [inPos_iff, InT.iff_open] at hw
    rw [litIff, InT.iff_open] at hlw
    rcases d with ⟨rfl, rfl, ne⟩ | ⟨rfl, rfl, lt⟩ | ⟨rfl, rfl, lt⟩
    · exact ne (by rw [← hw.2 rfl, hlw.2 rfl])
    · have := hlw.1.length_le; have := hw.2 rfl; omega
    · have := hw.1.length_le; have := hlw.2 rfl; omega
  right
  have nv : v ≠ .atom "disjoint" := fun e => d (disj.mp e)
  let tag : String := if t₁ = "open" ∧ t₂ = "open" then "open" else "closed"
  refine ⟨.tuple #[.atom tag, Term.list r], ?_, ⟨tag, r, rfl, by simp only [tag]; split <;> simp, hr⟩, fun w => ?_⟩
  · split
    · exact absurd rfl nv
    · simp only [Term.list] at zip
      by_cases o₁ : t₁ = "open" <;> by_cases o₂ : t₂ = "open" <;>
        simp [tag, o₁, o₂, Erlang.erlang.«==/2», Lynx.Except.andAlso, zip]
  rw [inPos_iff, inPos_iff, litIff, InT.iff_open, InT.iff_open (l := l₁), InT.iff_open (l := l₂), semr w]
  have nd : ¬Disj t₁ t₂ l₁.length l₂.length := d
  simp only [Disj, not_or, not_and] at nd
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> simp [tag, len] at nd ⊢
  all_goals first
    | (rw [Nat.max_eq_right nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩)
    | (rw [Nat.max_eq_left nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩)
    | (rw [nd, Nat.max_self]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b, c⟩, fun ⟨⟨a, c⟩, b, _⟩ => ⟨⟨a, b⟩, c⟩⟩)

theorem list_compare_inT {c : Bool} (sem : ElemSem E K V den Safe) : ∀ {l l' : List Term} {v : List V},
    (∀ e ∈ l, E e) → (∀ e ∈ l', E e) → compare (fuel (Term.list l) (Term.list l')) (Term.list l) (Term.list l') = .eq → InT den c l' v → InT den c l v
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, _, e, _ => by simp [Term.list] at e
  | _ :: _, [], _, _, _, e, _ => by simp [Term.list] at e
  | x :: l, y :: l', [], _, _, _, h => h.elim
  | x :: l, y :: l', z :: v, hl, hl', e, h => by
    simp only [Term.list, compare_cons, Ordering.then_eq_eq] at e
    exact ⟨sem.resp (hl x List.mem_cons_self) (hl' y List.mem_cons_self) e.1 h.1,
      list_compare_inT sem (fun e m => hl e (List.mem_cons_of_mem _ m)) (fun e m => hl' e (List.mem_cons_of_mem _ m))
        e.2 h.2⟩

open Classical in
/-- The valuation of tuple literals that a tuple of values induces, up to comparison. -/
noncomputable def valT (E : Term → Prop) (den : Term → V → Prop) (v : List V) (t : Term) : Bool :=
  decide (∃ t', compare (fuel t t') t t' = .eq ∧ TupleLit E t' ∧ LitSem den t' v)

theorem valT_resp (v : List V) : Resp (valT E den v) := by
  intro a b h
  simp only [valT]
  congr 1
  apply propext
  constructor
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans h e, rest⟩

theorem valT_true {v : List V} {t : Term} (ht : TupleLit E t) (h : LitSem den t v) : valT E den v t = Bool.true := by
  simp only [valT, decide_eq_true_eq]
  exact ⟨t, compare_self t, ht, h⟩

theorem valT_lit (sem : ElemSem E K V den Safe) {v : List V} {t : Term} (ht : TupleLit E t) (h : valT E den v t = Bool.true) :
    LitSem den t v := by
  simp only [valT, decide_eq_true_eq] at h
  obtain ⟨t', e, ⟨k', tag', l', rfl, -, hl'⟩, ⟨k'', tag'', l'', e', hv⟩⟩ := h
  obtain ⟨k, tag, l, rfl, -, hl⟩ := ht
  have e'' := e'
  simp only [Term.tuple.injEq] at e''
  have t₁ : Term.atom tag' = Term.atom tag'' := by have := congrArg (fun a : Array Term => a[1]?) e''; simpa using this
  have t₂ : Term.list l' = Term.list l'' := by have := congrArg (fun a : Array Term => a[2]?) e''; simpa using this
  simp only [Term.atom.injEq] at t₁
  rw [← t₁, ← list_inj t₂] at hv
  simp only [compare_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
    Ordering.then_eq_eq, List.compareLex_cons_cons] at e
  obtain ⟨-, -, et, el, -⟩ := e
  simp only [compare_eq_atom, Term.atom.injEq] at et
  subst et
  exact ⟨k, tag, l, rfl, list_compare_inT sem hl hl' el hv⟩

theorem valT_iff (sem : ElemSem E K V den Safe) {v : List V} {t : Term} (ht : TupleLit E t) :
    valT E den v t = Bool.true ↔ LitSem den t v := ⟨valT_lit sem ht, valT_true ht⟩

/-- A line whose values its negations cover is empty, whether some element is empty or not. -/
theorem top_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    (S : List (Term × Term)) (hS : Safe S) {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed") (el : ∀ e ∈ l, E e)
    {negs : List Term} (lits : ∀ t ∈ negs, TupleLit E t)
    (cover : ∀ v, InT den (tag == "closed") l v → ∃ N ∈ negs, LitSem den N v) :
    Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4» (D m) (.atom tag) (Term.list l) (Term.list negs) (.map S) =
      .ok (.atom "true") := by
  obtain ⟨b, check, full⟩ := elements_check ops S l el
  rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
  simp only [check m hm, Lynx.Except.ok_bind]
  cases b
  rotate_left
  · simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
  have full := full rfl
  have hm' : K ≤ m := by omega
  have nonempty : negs ≠ [] := by
    rintro rfl
    obtain ⟨v, hv, -⟩ := tuple_witness sem hS l full (tag == "closed") 0
    obtain ⟨N, mN, -⟩ := cover v hv
    simp at mN
  have notNil : Erlang.erlang.«==/2» (Term.list negs) .nil = .ok (.atom "false") := by
    cases negs with
    | nil => exact absurd rfl nonempty
    | cons x xs => simp [Erlang.erlang.«==/2», Term.list, Term.false]
  simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
  have := line_complete ops dops sem hm' S hS negs lits (tag == "closed") l full cover
  rcases g with rfl | rfl <;> simpa using this

/-- No tuple value along the path, outside the negated literals, satisfies the BDD. -/
def ValUnsat (E : Term → Prop) (den : Term → V → Prop) (pos : Term) (negs : List Term) (r : Term) : Prop :=
  ∀ v, InPos den pos v → (∀ N ∈ negs, ¬LitSem den N v) → eval (valT E den v) r = Bool.false

theorem cover_of_unsat {pos : Term} {negs : List Term} {v : List V}
    (h : InPos den pos v → (∀ N ∈ negs, ¬LitSem den N v) → False) (hv : InPos den pos v) :
    ∃ N ∈ negs, LitSem den N v :=
  Classical.byContradiction fun none => h hv fun N mN hN => none ⟨N, mN, hN⟩

theorem tuple_bdd_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos → (∀ t ∈ negs, TupleLit E t) → ValUnsat E den pos negs r →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos →
    (∀ t ∈ negs, TupleLit E t) → ValUnsat E den pos negs r →
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits g
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    simp only
    exact top_val ops dops sem hm S hS gt el lits fun v hv =>
      cover_of_unsat (fun hv' nn => by have := g v hv' nn; simp at this) (inPos_iff.mpr hv)
  · intro ok _ pos negs _ _ _
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    split <;> simp_all
  · intro ok k x y okl okLit pos negs hp lits g
    have hl := okLit _ okl
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_sem ops sem hm hp hl with ⟨empty, -⟩ | ⟨pos', run, hp', sem'⟩
    · simp [empty]
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    simp [run]
    refine top_val ops dops sem hm S hS gt el lits fun v hv => ?_
    obtain ⟨hpos, hlit⟩ := (sem' v).mp (inPos_iff.mpr hv)
    refine cover_of_unsat (fun hv' nn => ?_) hpos
    have := g v hv' nn
    rw [eval_leaf, valT_true hl.1 hlit] at this
    cases this
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits g
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    have dPart : Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list (lit :: negs)) d (.map S) =
        .ok (.atom "true") := by
      refine idd okLit' pos (lit :: negs) hp (fun t m => ?_) fun v hv nn => ?_
      · rcases List.mem_cons.mp m with rfl | m
        · exact hl.1
        · exact lits t m
      have nl : valT E den v lit = Bool.false := by
        cases e : valT E den v lit
        · rfl
        · exact absurd (valT_lit sem hl.1 e) (nn lit List.mem_cons_self)
      have := g v hv fun N mN => nn N (List.mem_cons_of_mem _ mN)
      simp only [eval_node, nl] at this
      simp at this
      exact this.2
    have uPart := iu okLit' pos negs hp lits fun v hv nn => by
      have := g v hv nn
      simp only [eval_node] at this
      cases hu' : eval (valT E den v) u
      · rfl
      · simp [hu'] at this
    rw [list_cons] at dPart
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_sem ops sem hm ⟨tag, l, rfl, gt, el⟩ hl with ⟨empty, -⟩ | ⟨pos2, run, hp2, sem2⟩
    · simp [empty, dPart, uPart, Lynx.Except.andAlso]
    have cRes := ic okLit' pos2 negs hp2 lits fun v hv nn => by
      obtain ⟨hpos, hlit⟩ := (sem2 v).mp hv
      have := g v hpos nn
      simp only [eval_node, valT_true hl.1 hlit] at this
      simp at this
      exact this.1
    obtain ⟨tag2, l2, rfl, -⟩ := hp2
    simp [run, dPart, uPart, Lynx.Except.andAlso, cRes]

end Elixir.STTDescrProofsTest
