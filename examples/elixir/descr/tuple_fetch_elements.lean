namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple_fetch_element/3` takes the element at an index, or the top or empty type past the elements. -/
theorem fetch_element (tag : String) (g : tag = "open" ∨ tag = "closed") :
    ∀ (l : List Term) (i : Nat), Elixir.Module.Types.Descr.«tuple_fetch_element/3» (Term.list l) (.integer i) (.atom tag) =
      .ok (if h : i < l.length then .tuple #[l[i], .atom "false"]
        else if tag = "open" then .tuple #[.atom "term", .atom "true"] else .tuple #[.map [], .atom "true"])
  | [], i => by
    rcases g with rfl | rfl <;> simp [Elixir.Module.Types.Descr.«tuple_fetch_element/3», Term.list]
  | x :: l, 0 => by simp [Elixir.Module.Types.Descr.«tuple_fetch_element/3», Term.list]
  | x :: l, j + 1 => by
    have ih := fetch_element tag g l j
    have ne : ((j + 1 : Nat) : Int) ≠ 0 := by omega
    rw [Elixir.Module.Types.Descr.«tuple_fetch_element/3».eq_def]
    simp only [Term.list] at ih ⊢
    by_cases h : j < l.length <;> simp_all
    intro h'; omega

theorem do_take : ∀ (l₁ : List Term) (x : Term) (l₂ acc : List Term),
    Elixir.Module.Types.Descr.«do_tuple_take_element/3» (Term.list (l₁ ++ x :: l₂)) (.integer l₁.length) (Term.list acc) =
      .ok (.tuple #[x, Term.list (acc.reverse ++ l₁ ++ l₂)])
  | [], x, l₂, acc => by
    simp [Elixir.Module.Types.Descr.«do_tuple_take_element/3», Term.list, reverse_list]
  | h :: l₁, x, l₂, acc => by
    have ih := do_take l₁ x l₂ (h :: acc)
    have ne : ((l₁.length + 1 : Nat) : Int) ≠ 0 := by omega
    rw [Elixir.Module.Types.Descr.«do_tuple_take_element/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp_all

theorem do_take_short : ∀ (l acc : List Term) (i : Nat), l.length ≤ i →
    Elixir.Module.Types.Descr.«do_tuple_take_element/3» (Term.list l) (.integer i) (Term.list acc) = .ok (.atom "error")
  | [], acc, i, _ => by simp [Elixir.Module.Types.Descr.«do_tuple_take_element/3»]
  | h :: l, acc, 0, le => by simp at le
  | h :: l, acc, j + 1, le => by
    have ih := do_take_short l (h :: acc) j (by simp at le; omega)
    have ne : ((j + 1 : Nat) : Int) ≠ 0 := by omega
    rw [Elixir.Module.Types.Descr.«do_tuple_take_element/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp_all

/-- `tuple_take_element/3` splits a literal at an index into the element there and a literal of the others. -/
theorem take_mid (tag : String) (g : tag = "open" ∨ tag = "closed") (l₁ : List Term) (x : Term) (l₂ : List Term) :
    ∃ k : Int, Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list (l₁ ++ x :: l₂)) (.integer l₁.length)
      (.atom tag) = .ok (.tuple #[x, .tuple #[.integer k, .atom tag, Term.list (l₁ ++ l₂)]]) ∧
      KeyOk (.tuple #[.integer k, .atom tag, Term.list (l₁ ++ l₂)]) := by
  obtain ⟨k, run, key⟩ := leaf_new_key tag g (l₁ ++ l₂)
  refine ⟨k, ?_, key⟩
  have := do_take l₁ x l₂ []
  simp only [List.reverse_nil, List.nil_append] at this
  simp [Elixir.Module.Types.Descr.«tuple_take_element/3», this, Elixir.Module.Types.Descr.«tuple_new/2», run]

theorem take_closed_short (l : List Term) (i : Nat) (h : l.length ≤ i) :
    Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i) (.atom "closed") = .ok (.atom "empty") := by
  have := do_take_short l [] i h
  simp [Elixir.Module.Types.Descr.«tuple_take_element/3», Term.list] at this ⊢
  simp [this]

theorem take_open_short (l : List Term) (i : Nat) (h : l.length ≤ i) :
    ∃ k : Int, Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i) (.atom "open") =
      .ok (.tuple #[.atom "term", .tuple #[.integer k, .atom "open",
        Term.list (l ++ List.replicate (i - l.length) (.atom "term"))]]) ∧
      KeyOk (.tuple #[.integer k, .atom "open", Term.list (l ++ List.replicate (i - l.length) (.atom "term"))]) := by
  obtain ⟨k, run, key⟩ := leaf_new_key "open" (Or.inl rfl) (l ++ List.replicate (i - l.length) (.atom "term"))
  refine ⟨k, ?_, key⟩
  have := do_take_short l [] i h
  simp [Elixir.Module.Types.Descr.«tuple_take_element/3», Term.list] at this ⊢
  simp [this, Erlang.erlang.«==/2», fill_list l i h, Elixir.Module.Types.Descr.«tuple_new/2», run]

section
variable {V : Type} {den : Term → V → Prop}

/-- Values of a literal, split at one of its elements. -/
theorem InT.split {c : Bool} : ∀ (l₁ : List Term) (x : Term) (l₂ : List Term) (v₁ : List V) (y : V) (v₂ : List V),
    l₁.length = v₁.length →
    (InT den c (l₁ ++ x :: l₂) (v₁ ++ y :: v₂) ↔ den x y ∧ InT den c (l₁ ++ l₂) (v₁ ++ v₂))
  | [], x, l₂, [], y, v₂, _ => Iff.rfl
  | [], _, _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, _, [], _, _, h => by simp at h
  | e :: l₁, x, l₂, z :: v₁, y, v₂, h => by
    have ih : InT den c (l₁ ++ x :: l₂) (v₁ ++ y :: v₂) ↔ den x y ∧ InT den c (l₁ ++ l₂) (v₁ ++ v₂) :=
      InT.split l₁ x l₂ v₁ y v₂ (by simpa using h)
    simp only [List.cons_append, InT, ih]
    exact ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨b, a, c⟩ => ⟨a, b, c⟩⟩

theorem InT.terms (hterm : ∀ y, den (.atom "term") y) {c : Bool} :
    ∀ (n : Nat) (w : List V), n = w.length → InT den c (List.replicate n (.atom "term")) w
  | 0, [], _ => trivial
  | n + 1, y :: w, h => ⟨hterm y, InT.terms hterm n w (by simpa using h)⟩
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h

theorem InT.open_any (hterm : ∀ y, den (.atom "term") y) :
    ∀ (n : Nat) (w : List V), n ≤ w.length → InT den Bool.false (List.replicate n (.atom "term")) w
  | 0, [], _ => trivial
  | 0, _ :: _, _ => rfl
  | n + 1, y :: w, h => ⟨hterm y, InT.open_any hterm n w (by simp at h; omega)⟩
  | _ + 1, [], h => by simp at h

/-- Values of an open literal shorter than an index, split at that index. -/
theorem InT.split_short (hterm : ∀ y, den (.atom "term") y) :
    ∀ (l : List Term) (v₁ : List V) (y : V) (v₂ : List V), l.length ≤ v₁.length →
      (InT den Bool.false l (v₁ ++ y :: v₂) ↔
        InT den Bool.false (l ++ List.replicate (v₁.length - l.length) (.atom "term")) (v₁ ++ v₂))
  | [], v₁, y, v₂, _ => by
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    refine ⟨fun _ => InT.open_any hterm _ _ (by simp), fun _ => ?_⟩
    cases v₁ <;> exact rfl
  | e :: l, [], y, v₂, h => by simp at h
  | e :: l, z :: v₁, y, v₂, h => by
    have ih := InT.split_short hterm l v₁ y v₂ (by simpa using h)
    simp only [List.cons_append, InT, List.length_cons, Nat.add_sub_add_right, ih]

theorem InT.split_closed : ∀ {l : List Term} {v₁ : List V} {y : V} {v₂ : List V}, l.length ≤ v₁.length →
    ¬InT den Bool.true l (v₁ ++ y :: v₂) := by
  intro l v₁ y v₂ h h'
  have := h'.closed_length
  simp at this; omega

end

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Lines of tuple BDDs: a tag, element types, and negated literals. -/
def TLine (E : Term → Prop) (L : Term) : Prop :=
  ∃ (tag : String) (l negs : List Term), L = .tuple #[.atom tag, Term.list l, Term.list negs] ∧
    (tag = "open" ∨ tag = "closed") ∧ (∀ e ∈ l, E e) ∧ ∀ t ∈ negs, TupleLit E t

/-- Tuples of values in a line. -/
def InLine (den : Term → V → Prop) (L : Term) (v : List V) : Prop :=
  ∃ (tag : String) (l negs : List Term), L = .tuple #[.atom tag, Term.list l, Term.list negs] ∧
    InT den (tag == "closed") l v ∧ ∀ N ∈ negs, ¬LitSem den N v

theorem inLine_iff {tag : String} {l negs : List Term} {v : List V} :
    InLine den (.tuple #[.atom tag, Term.list l, Term.list negs]) v ↔
      InT den (tag == "closed") l v ∧ ∀ N ∈ negs, ¬LitSem den N v := by
  constructor
  · rintro ⟨tag', l', negs', e, h, hn⟩
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₁
    rw [e₁, list_inj e₂, list_inj e₃]
    exact ⟨h, hn⟩
  · intro h; exact ⟨tag, l, negs, rfl, h⟩

/-- `tuple_bdd_to_dnf/4` lists the lines of a BDD: the values of the path through it, outside its negations. -/
theorem dnf_tuple (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {ok : Term → Prop}
    {r : Term} (wr : Bdd ok r) (okT : ∀ t, ok t → TupleOk E t) :
    ∀ (acc : List Term) (pos : Term) (negs : List Term), TuplePos E pos → (∀ t ∈ negs, TupleLit E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) (Term.list acc) pos (Term.list negs) r =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, TLine E L) ∧
        ∀ v, (∃ L ∈ lines, InLine den L v) ↔
          (InPos den pos v ∧ (∀ N ∈ negs, ¬LitSem den N v) ∧ eval (valT E den v) r = Bool.true) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) →
    ∀ (acc : List Term) (pos : Term) (negs : List Term), TuplePos E pos → (∀ t ∈ negs, TupleLit E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) (Term.list acc) pos (Term.list negs) r =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, TLine E L) ∧
        ∀ v, (∃ L ∈ lines, InLine den L v) ↔
          (InPos den pos v ∧ (∀ N ∈ negs, ¬LitSem den N v) ∧ eval (valT E den v) r = Bool.true))
    ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ acc pos negs hp lits
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    refine ⟨[.tuple #[.atom tag, Term.list l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp [Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp [inLine_iff, inPos_iff]
  · intro ok _ acc pos negs _ _
    refine ⟨[], ?_, by simp, fun v => by simp⟩
    rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp
  · intro ok k x y okl okLit acc pos negs hp lits
    have hl := okLit _ okl
    rcases inter_sem ops sem hm hp hl with ⟨empty, none⟩ | ⟨pos', run, hp', sem'⟩
    · refine ⟨[], ?_, by simp, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp [empty]
      · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and, eval_leaf]
        intro hv _ e
        exact none v hv (valT_lit sem hl.1 e)
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    refine ⟨[.tuple #[.atom tag, Term.list l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp [run, Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp only [List.mem_singleton, exists_eq_left, inLine_iff, eval_leaf, valT_iff sem hl.1]
      rw [← inPos_iff, sem' v]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc pos negs hp lits
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    obtain ⟨Lu, ru, tu, su⟩ := iu okLit' acc pos negs hp lits
    have lits' : ∀ t ∈ lit :: negs, TupleLit E t := fun t mt => by
      rcases List.mem_cons.mp mt with rfl | mt
      · exact hl.1
      · exact lits t mt
    obtain ⟨Lc, runC, tc, sc⟩ : ∃ Lc,
        ((Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok (.atom "empty") ∧ Lc = []) ∨
          ∃ tag2 l2, Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit =
              .ok (.tuple #[.atom tag2, Term.list l2]) ∧
            Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) (Term.list (Lu ++ acc)) (.tuple #[.atom tag2, Term.list l2])
              (Term.list negs) c = .ok (Term.list (Lc ++ (Lu ++ acc)))) ∧ (∀ L ∈ Lc, TLine E L) ∧
          ∀ v, (∃ L ∈ Lc, InLine den L v) ↔
            (InPos den pos v ∧ LitSem den lit v ∧ (∀ N ∈ negs, ¬LitSem den N v) ∧ eval (valT E den v) c = Bool.true) := by
      rcases inter_sem ops sem hm hp hl with ⟨empty, none⟩ | ⟨pos2, run, hp2, sem2⟩
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
    · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]
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
    · have split : (∃ L ∈ Ld ++ Lc ++ Lu, InLine den L v) ↔
          (∃ L ∈ Ld, InLine den L v) ∨ (∃ L ∈ Lc, InLine den L v) ∨ (∃ L ∈ Lu, InLine den L v) := by
        constructor
        · rintro ⟨L, mL, hL⟩
          simp only [List.mem_append] at mL
          rcases mL with (mL | mL) | mL
          · exact Or.inl ⟨L, mL, hL⟩
          · exact Or.inr (Or.inl ⟨L, mL, hL⟩)
          · exact Or.inr (Or.inr ⟨L, mL, hL⟩)
        · rintro (⟨L, mL, hL⟩ | ⟨L, mL, hL⟩ | ⟨L, mL, hL⟩) <;> exact ⟨L, by simp [mL], hL⟩
      rw [split, sd v, sc v, su v, eval_node]
      by_cases hlit : LitSem den lit v
      · have e : valT E den v lit = Bool.true := valT_true hl.1 hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inl ⟨a, b, c⟩) (fun c => Or.inr ⟨a, b, c⟩)⟩
      · have e : valT E den v lit = Bool.false := by
          cases h' : valT E den v lit
          · rfl
          · exact absurd (valT_lit sem hl.1 h') hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inr ⟨a, b, c⟩) (fun c => Or.inl ⟨a, b, c⟩)⟩

/-- `tuple_line_elements_empty?/2` finds an empty element, when there is one. -/
theorem elements_exact (ops : ElemOk E K) (sem : ElemSem E K V den Safe) (hS : Safe []) (l : List Term)
    (hl : ∀ e ∈ l, E e) : ∃ b, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D m)
      (Term.list l) (.map []) = .ok (boolAtom b)) ∧ (b = Bool.false → ∀ e ∈ l, Full E K [] e) ∧
      (b = Bool.true → ∃ e ∈ l, ∀ y, ¬den e y) := by
  have each : ∀ e ∈ l, ∃ b, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map []) = .ok (boolAtom b) :=
    fun e me => ops.empty (hl e me) []
  classical
  let res : Term → Bool := fun e => if h : e ∈ l then Classical.choose (each e h) else Bool.false
  have hres : ∀ e ∈ l, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map []) = .ok (boolAtom (res e)) := by
    intro e me m' h
    simp only [res, dite_eq_left me]
    exact Classical.choose_spec (each e me) m' h
  refine ⟨l.any res, fun m hm => ?_, fun no e me => ⟨hl e me, fun m' h => ?_⟩, fun yes => ?_⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    simp only [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2»]
    refine any_list _ _ _ _ res l fun x mx => ?_
    rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2»]
    exact hres x mx n hn
  · have := List.any_eq_false.mp no e me
    rw [hres e me m' h]
    simp_all [boolAtom]
  · obtain ⟨e, me, he⟩ := List.any_eq_true.mp yes
    refine ⟨e, me, fun y hy => ?_⟩
    have := (sem.empty (hl e me) hS (Nat.le_refl K) (hres e me K (Nat.le_refl K))).mp he
    exact this y hy

/-- Lines either hold a tuple of values or are empty. -/
theorem line_keep (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {L : Term}
    (hL : TLine E L) : ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ v, InLine den L v) := by
  obtain ⟨tag, l, negs, rfl, gt, el, lits⟩ := hL
  obtain ⟨b, check, full, empty⟩ := elements_exact ops sem hS l el
  cases b
  · have full := full rfl
    by_cases ex : ∃ v, InLine den (.tuple #[.atom tag, Term.list l, Term.list negs]) v
    · refine ⟨Bool.true, fun m acc hm => ?_, by simp [ex]⟩
      obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      obtain ⟨v, hvL⟩ := ex
      obtain ⟨hv, hn'⟩ := inLine_iff.mp hvL
      have f := line_false ops dops sem (m := n) (by omega) [] hS negs lits (tag == "closed") l el v hv hn'
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_with_negations/1-fun-0-/2».pure]
      rcases gt with rfl | rfl <;>
        simp_all [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_with_negations/1-fun-0-/2»,
          Elixir.Module.Types.Descr.«tuple_line_empty?/3», check n (by omega), Lynx.Except.orElse, Lynx.Term.isMember]
    · refine ⟨Bool.false, fun m acc hm => ?_, by simp [ex]⟩
      obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      have t := line_complete ops dops sem (m := n) (by omega) [] hS negs lits (tag == "closed") l full
        fun v hv => Classical.byContradiction fun none => ex ⟨v, inLine_iff.mpr ⟨hv, fun N mN hN => none ⟨N, mN, hN⟩⟩⟩
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_with_negations/1-fun-0-/2».pure]
      rcases gt with rfl | rfl <;>
        simp_all [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_with_negations/1-fun-0-/2»,
          Elixir.Module.Types.Descr.«tuple_line_empty?/3», check n (by omega), Lynx.Except.orElse, Lynx.Term.isMember]
  · obtain ⟨e, me, he⟩ := empty rfl
    refine ⟨Bool.false, fun m acc hm => ?_, ?_⟩
    · obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_with_negations/1-fun-0-/2».pure]
      simp [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_with_negations/1-fun-0-/2», check n (by omega),
        Lynx.Except.orElse, Lynx.Term.isMember]
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro v hv
      obtain ⟨hv, -⟩ := inLine_iff.mp hv
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem me
      obtain ⟨v₁, y, v₂, -, -, hy, -⟩ := (InT.mid l₁ e l₂).mp hv
      exact he y hy

/-- Folds whose steps compute a function of the element and the accumulator. -/
theorem foldl1_det {K : Nat} (f : Term) (g : Term → Term → Term) :
    ∀ l : List Term, (∀ x ∈ l, ∀ a m, K ≤ m → (D m).pure f #[x, a] = .ok (g x a)) →
      ∀ acc m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list l) = .ok (l.foldl (fun a x => g x a) acc) := by
  intro l
  induction l with
  | nil => intro _ acc m _; simp [Erlang.lists.«foldl_1/3»]
  | cons x xs ih =>
    intro step acc m hm
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at ih ⊢
    simp only [step x List.mem_cons_self acc m hm, Lynx.Except.ok_bind, List.foldl_cons]
    exact ih (fun y my => step y (List.mem_cons_of_mem _ my)) _ m hm

theorem foldl_det {K : Nat} (mo nm : String) (caps : Array Term) (g : Term → Term → Term) (l : List Term)
    (step : ∀ x ∈ l, ∀ a m, K ≤ m → (D m).pure (.function mo nm 2 caps) #[x, a] = .ok (g x a)) (acc : Term) {m : Nat}
    (hm : K ≤ m) : Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) =
      .ok (l.foldl (fun a x => g x a) acc) := by
  have := foldl1_det (.function mo nm 2 caps) g l step acc m hm
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem foldl_filter (keep : Term → Bool) : ∀ (l acc : List Term),
    l.foldl (fun a x => if keep x then Term.cons x a else a) (Term.list acc) = Term.list ((l.filter keep).reverse ++ acc)
  | [], acc => by simp
  | x :: l, acc => by
    have ih := foldl_filter keep l
    cases h : keep x
    · simp [h, ih]
    · have := ih (x :: acc)
      simp only [Term.list] at this
      simp [h, this]

/-- `tuple_bdd_to_dnf_with_negations/1` lists the non-empty lines of a BDD. -/
theorem dnf_neg (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {m : Nat}
    (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (TLit E) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_with_negations/1» (D m) r =
        .ok (Term.list lines) ∧ (∀ L ∈ lines, TLine E L ∧ ∃ v, InLine den L v) ∧
      ∀ v, eval (valT E den v) r = Bool.true ↔ ∃ L ∈ lines, InLine den L v := by
  obtain ⟨all, run, tl, sl⟩ := dnf_tuple ops sem (m := m) (by omega) wr (fun t h => h.1) [] (.tuple #[.atom "open", .nil]) []
    ⟨"open", [], rfl, Or.inl rfl, by simp⟩ (by simp)
  have keeps : ∀ L ∈ all, ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ v, InLine den L v) :=
    fun L mL => line_keep ops dops sem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc)) ∧ (keep L = Bool.true ↔ ∃ v, InLine den L v) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact Classical.choose_spec (keeps L mL)
  have fold := foldl_det (K := K + 2) "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all (fun x mx a m hm => (hk x mx).1 m a hm) .nil hm
  have e := foldl_filter keep all []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all.filter keep).reverse, ?_, fun L mL => ?_, fun v => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_with_negations/1»]
    have run' : Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r =
        .ok (Term.list all) := by simpa using run
    simp only [run', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all)) =
        Erlang.lists.«foldl/3» (D m) (.function "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[])
          .nil (Term.list all) from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact ⟨tl L mL.1, (hk L mL.1).2.mp mL.2⟩
  · have hp : InPos den (.tuple #[.atom "open", .nil]) v := ⟨"open", [], rfl, InT.open_nil v⟩
    rw [← (by simpa [hp] using sl v : (∃ L ∈ all, InLine den L v) ↔ eval (valT E den v) r = Bool.true)]
    constructor
    · rintro ⟨L, mL, hL⟩
      exact ⟨L, by simp [mL, (hk L mL).2.mpr ⟨v, hL⟩], hL⟩
    · rintro ⟨L, mL, hL⟩
      simp only [List.mem_reverse, List.mem_filter] at mL
      exact ⟨L, mL.1, hL⟩

/-- Folds whose steps keep a relation between the elements folded so far and the accumulator. -/
theorem foldl1_rel {K : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ ∀ m, K ≤ m → (D m).pure f #[x, a] = .ok a') :
    ∀ (rest pre : List Term) acc, (∀ x ∈ rest, x ∈ l) → R pre acc →
      ∃ r, R (pre ++ rest) r ∧ ∀ m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r := by
  intro rest
  induction rest with
  | nil => intro pre acc _ h; exact ⟨acc, by simpa using h, fun m _ => by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc sub h
    obtain ⟨a', h', run⟩ := step pre x acc (sub x List.mem_cons_self) h
    obtain ⟨r, hr, rest⟩ := ih (pre ++ [x]) a' (fun y my => sub y (List.mem_cons_of_mem _ my)) h'
    refine ⟨r, by simpa using hr, fun m hm => ?_⟩
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at rest ⊢
    simp only [run m hm, Lynx.Except.ok_bind]
    exact rest m hm

theorem foldl_rel {K : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ ∀ m, K ≤ m →
      (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (h : R [] acc) :
    ∃ r, R l r ∧ ∀ m, K ≤ m → Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldl1_rel (.function mo nm 2 caps) R l step l [] acc (fun _ h => h) h
  refine ⟨r, by simpa using hr, fun m hm => ?_⟩
  have := run m hm
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using this
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem foldl1_rel_at {m : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ (D m).pure f #[x, a] = .ok a') :
    ∀ (rest pre : List Term) acc, (∀ x ∈ rest, x ∈ l) → R pre acc →
      ∃ r, R (pre ++ rest) r ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r := by
  intro rest
  induction rest with
  | nil => intro pre acc _ h; exact ⟨acc, by simpa using h, by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc sub h
    obtain ⟨a', h', run⟩ := step pre x acc (sub x List.mem_cons_self) h
    obtain ⟨r, hr, rest⟩ := ih (pre ++ [x]) a' (fun y my => sub y (List.mem_cons_of_mem _ my)) h'
    refine ⟨r, by simpa using hr, ?_⟩
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at rest ⊢
    simp only [run, Lynx.Except.ok_bind]
    exact rest

/-- Folds at a call depth whose steps keep a relation between the elements folded so far and the accumulator. -/
theorem foldl_rel_at {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧
      (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (h : R [] acc) :
    ∃ r, R l r ∧ Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldl1_rel_at (.function mo nm 2 caps) R l step l [] acc (fun _ h => h) h
  refine ⟨r, by simpa using hr, ?_⟩
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using run
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at run
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using run

theorem foldl1_lists_at {m : Nat} (f : Term) (h : Term → List Term) :
    ∀ l : List Term, (∀ x ∈ l, ∀ (A : List Term), (D m).pure f #[x, Term.list A] = .ok (Term.list (h x ++ A))) →
      ∀ A, Erlang.lists.«foldl_1/3» (D m) f (Term.list A) (Term.list l) =
        .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  intro l
  induction l with
  | nil => intro _ A; simp [Erlang.lists.«foldl_1/3»]
  | cons x xs ih =>
    intro step A
    rw [Erlang.lists.«foldl_1/3».eq_def]
    have tail := ih (fun y my => step y (List.mem_cons_of_mem _ my)) (h x ++ A)
    simp only at tail step ⊢
    simp only [step x List.mem_cons_self A, Lynx.Except.ok_bind]
    simpa using tail

/-- Folds at a call depth whose steps prepend a list to the accumulator. -/
theorem foldl_lists_at {m : Nat} (mo nm : String) (caps : Array Term) (h : Term → List Term) (l : List Term)
    (step : ∀ x ∈ l, ∀ (A : List Term),
      (D m).pure (.function mo nm 2 caps) #[x, Term.list A] = .ok (Term.list (h x ++ A))) (A : List Term) :
    Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) (Term.list A) (Term.list l) =
      .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  have := foldl1_lists_at (.function mo nm 2 caps) h l step A
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

/-- Folds whose steps prepend a list to the accumulator. -/
theorem foldl1_lists {K : Nat} (f : Term) (h : Term → List Term) :
    ∀ l : List Term, (∀ x ∈ l, ∀ (A : List Term) m, K ≤ m → (D m).pure f #[x, Term.list A] = .ok (Term.list (h x ++ A))) →
      ∀ A m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f (Term.list A) (Term.list l) =
        .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  intro l
  induction l with
  | nil => intro _ A m _; simp [Erlang.lists.«foldl_1/3»]
  | cons x xs ih =>
    intro step A m hm
    rw [Erlang.lists.«foldl_1/3».eq_def]
    have tail := ih (fun y my => step y (List.mem_cons_of_mem _ my)) (h x ++ A) m hm
    simp only at tail step ⊢
    simp only [step x List.mem_cons_self A m hm, Lynx.Except.ok_bind]
    simpa using tail

theorem foldl_lists {K : Nat} (mo nm : String) (caps : Array Term) (h : Term → List Term) (l : List Term)
    (step : ∀ x ∈ l, ∀ (A : List Term) m, K ≤ m →
      (D m).pure (.function mo nm 2 caps) #[x, Term.list A] = .ok (Term.list (h x ++ A))) (A : List Term) {m : Nat}
    (hm : K ≤ m) : Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) (Term.list A) (Term.list l) =
      .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  have := foldl1_lists (.function mo nm 2 caps) h l step A m hm
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Pairs of an element type and a tuple type, as tuples split at an index. -/
def PairOk (E : Term → Prop) (p : Term) : Prop := ∃ f b, p = .tuple #[f, b] ∧ E f ∧ TField E b

/-- A value and the remaining tuple of values in a pair. -/
def PairIn (E : Term → Prop) (den : Term → V → Prop) (p : Term) (y : V) (w : List V) : Prop :=
  ∃ f b, p = .tuple #[f, b] ∧ den f y ∧ denTF E den b w = Bool.true

theorem pairIn_iff {f b : Term} {y : V} {w : List V} :
    PairIn E den (.tuple #[f, b]) y w ↔ den f y ∧ denTF E den b w = Bool.true := by
  constructor
  · rintro ⟨f', b', e, h₁, h₂⟩
    simp only [Term.tuple.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact ⟨h₁, h₂⟩
  · intro h; exact ⟨f, b, rfl, h⟩

theorem tleaf_field {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e)
    (key : KeyOk (.tuple #[.integer k, .atom tag, Term.list l])) : TField E (.tuple #[.integer k, .atom tag, Term.list l]) := by
  by_cases top : tag = "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨k, tag, l, rfl, g, hl⟩, ?_⟩, key⟩)
    rintro ⟨k', e⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₂
    cases l with
    | nil => exact top ⟨e₂, rfl⟩
    | cons _ _ => simp [Term.list] at e₃

/-- `tuple_take_element/3` splits a literal at an index into a pair, or finds no tuple long enough. -/
theorem take_pair (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) (i : Nat) : ∃ res, Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i)
      (.atom tag) = .ok res ∧
      ((res = .atom "empty" ∧ ∀ (v₁ : List V) y v₂, v₁.length = i → ¬InT den (tag == "closed") l (v₁ ++ y :: v₂)) ∨
        (PairOk E res ∧ res ≠ .atom "empty" ∧ (∀ y (w : List V), PairIn E den res y w → i ≤ w.length) ∧
          ∀ (v₁ : List V) y v₂, v₁.length = i →
          (InT den (tag == "closed") l (v₁ ++ y :: v₂) ↔ PairIn E den res y (v₁ ++ v₂)))) := by
  by_cases short : l.length ≤ i
  · rcases g with rfl | rfl
    · obtain ⟨k, run, key⟩ := take_open_short l i short
      have hl' : ∀ e ∈ l ++ List.replicate (i - l.length) (.atom "term"), E e := by
        intro e me
        rcases List.mem_append.mp me with me | me
        · exact hl e me
        · rw [List.eq_of_mem_replicate me]; exact ef.term
      refine ⟨_, run, Or.inr ⟨⟨_, _, rfl, ef.term, tleaf_field (Or.inl rfl) hl' key⟩, by simp, fun y w hw => ?_,
        fun v₁ y v₂ len => ?_⟩⟩
      · rw [pairIn_iff, denTF_leaf ef (Or.inl rfl) hl', vT_lit ef (Or.inl rfl) hl'] at hw
        have := hw.2.length_le
        simp at this; omega
      rw [pairIn_iff, denTF_leaf ef (Or.inl rfl) hl', vT_lit ef (Or.inl rfl) hl']
      have := InT.split_short (den := den) ef.den_term l v₁ y v₂ (by omega)
      rw [len] at this
      simpa [ef.den_term y] using this
    · exact ⟨_, take_closed_short l i short, Or.inl ⟨rfl, fun v₁ y v₂ len h => InT.split_closed (by omega) h⟩⟩
  · obtain ⟨l₁, x, l₂, rfl, len₁⟩ : ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ l₁.length = i := by
      refine ⟨l.take i, l[i]'(by omega), l.drop (i + 1), ?_, by simp; omega⟩
      simp
    obtain ⟨k, run, key⟩ := take_mid tag g l₁ x l₂
    rw [len₁] at run
    have hx : E x := hl x (by simp)
    have hl' : ∀ e ∈ l₁ ++ l₂, E e := fun e me => hl e (by
      rcases List.mem_append.mp me with me | me <;> simp [me])
    refine ⟨_, run, Or.inr ⟨⟨_, _, rfl, hx, tleaf_field g hl' key⟩, by simp, fun y w hw => ?_, fun v₁ y v₂ len => ?_⟩⟩
    · rw [pairIn_iff, denTF_leaf ef g hl', vT_lit ef g hl'] at hw
      have := hw.2.length_le
      simp at this; omega
    rw [pairIn_iff, denTF_leaf ef g hl', vT_lit ef g hl']
    exact InT.split l₁ x l₂ v₁ y v₂ (by omega)

open Classical in
/-- The pair a negated literal splits into at an index, if any. -/
noncomputable def splitH (i : Nat) (N : Term) : List Term :=
  match N with
  | .tuple ⟨[_, tag, els]⟩ =>
    match Elixir.Module.Types.Descr.«tuple_take_element/3» els (.integer i) tag with
    | .ok r => if r = .atom "empty" then [] else [r]
    | .error _ => []
  | _ => []

/-- `tuple_split_negative_pairs/2` splits the negated literals of a line at an index. -/
theorem split_pairs (ef : EF nd E V den tl K) (negs : List Term) (lits : ∀ N ∈ negs, TupleLit E N) (i : Nat) {m : Nat} :
    ∃ P, Elixir.Module.Types.Descr.«tuple_split_negative_pairs/2» (D m) (Term.list negs) (.integer i) = .ok (Term.list P) ∧
      (∀ p ∈ P, PairOk E p) ∧ ∀ (v₁ : List V) y v₂, v₁.length = i →
        ((∃ N ∈ negs, LitSem den N (v₁ ++ y :: v₂)) ↔ ∃ p ∈ P, PairIn E den p y (v₁ ++ v₂)) := by
  have each : ∀ N ∈ negs, (∀ (A : List Term) m', 0 ≤ m' →
      (D m').pure (.function "Elixir.Module.Types.Descr" "-tuple_split_negative_pairs/2-fun-0-" 2 #[.integer i])
        #[N, Term.list A] = .ok (Term.list (splitH i N ++ A))) ∧ (∀ p ∈ splitH i N, PairOk E p) ∧
      ∀ (v₁ : List V) y v₂, v₁.length = i →
        (LitSem den N (v₁ ++ y :: v₂) ↔ ∃ p ∈ splitH i N, PairIn E den p y (v₁ ++ v₂)) := by
    intro N mN
    obtain ⟨k, tag, l, rfl, g, hl⟩ := lits N mN
    obtain ⟨res, run, ⟨rfl, none⟩ | ⟨ok, ne, -, sem⟩⟩ := take_pair ef g hl i
    · have h : splitH i (.tuple #[.integer k, .atom tag, Term.list l]) = [] := by simp [splitH, run]
      refine ⟨fun A m' _ => ?_, by simp [h], fun v₁ y v₂ len => ?_⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_split_negative_pairs/2-fun-0-/2».pure, h]
        simp [Elixir.Module.Types.Descr.«-tuple_split_negative_pairs/2-fun-0-/3», run]
      · simp only [h, List.not_mem_nil, false_and, exists_false, iff_false]
        exact fun hN => none v₁ y v₂ len (lit_sem hN)
    · have h : splitH i (.tuple #[.integer k, .atom tag, Term.list l]) = [res] := by simp [splitH, run, ne]
      refine ⟨fun A m' _ => ?_, by simp [h, ok], fun v₁ y v₂ len => ?_⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_split_negative_pairs/2-fun-0-/2».pure, h]
        simp only [Elixir.Module.Types.Descr.«-tuple_split_negative_pairs/2-fun-0-/3», run, Lynx.Except.ok_bind]
        rfl
      · simp only [h, List.mem_singleton, exists_eq_left]
        rw [← sem v₁ y v₂ len]
        exact ⟨lit_sem, fun hv => ⟨k, tag, l, rfl, hv⟩⟩
  have fold := foldl_lists (K := 0) "Elixir.Module.Types.Descr" "-tuple_split_negative_pairs/2-fun-0-" #[.integer i]
    (splitH i) negs (fun N mN A m' h => (each N mN).1 A m' h) [] (m := m) (Nat.zero_le _)
  refine ⟨negs.reverse.flatMap (splitH i), ?_, fun p mp => ?_, fun v₁ y v₂ len => ?_⟩
  · simpa [Elixir.Module.Types.Descr.«tuple_split_negative_pairs/2»] using fold
  · simp only [List.mem_flatMap, List.mem_reverse] at mp
    obtain ⟨N, mN, mp⟩ := mp
    exact (each N mN).2.1 p mp
  · simp only [List.mem_flatMap, List.mem_reverse]
    constructor
    · rintro ⟨N, mN, hN⟩
      obtain ⟨p, mp, hp⟩ := ((each N mN).2.2 v₁ y v₂ len).mp hN
      exact ⟨p, ⟨N, mN, mp⟩, hp⟩
    · rintro ⟨p, ⟨N, mN, mp⟩, hp⟩
      exact ⟨N, mN, ((each N mN).2.2 v₁ y v₂ len).mpr ⟨p, mp, hp⟩⟩

/-- The union of the tuple types of pairs. -/
theorem union_pairs (P : List Term) (hP : ∀ p ∈ P, PairOk E p) :
    ∃ u, TField E u ∧ (∀ w, denTF E den u w = Bool.true ↔ ∃ p ∈ P, ∃ f b, p = .tuple #[f, b] ∧ denTF E den b w = Bool.true) ∧
      ∀ m, Erlang.lists.«foldl/3» (D m)
        (.function "Elixir.Module.Types.Descr" "-tuple_pair_projection_keeps_full_fst?/2-fun-0-" 2 #[])
        (.atom "bdd_bot") (Term.list P) = .ok u := by
  obtain ⟨u, ⟨tu, su⟩, run⟩ := foldl_rel (K := 0) "Elixir.Module.Types.Descr" "-tuple_pair_projection_keeps_full_fst?/2-fun-0-" #[]
    (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔
      ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ denTF E den b w = Bool.true) P
    (fun pre x a mx ⟨ta, sa⟩ => by
      obtain ⟨f, b, rfl, -, fb⟩ := hP x mx
      obtain ⟨r, run, tr, sr, -⟩ := tuple_union_lh (den := den) fb ta
      refine ⟨r, ⟨tr, fun w => ?_⟩, fun m _ => ?_⟩
      · rw [sr, Bool.or_eq_true, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_pair_projection_keeps_full_fst?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_pair_projection_keeps_full_fst?/2-fun-0-/2»] using run)
    (.atom "bdd_bot") ⟨Or.inr Bdd.bot, fun w => by simp [denTF_bot]⟩
  exact ⟨u, tu, su, fun m => run m (Nat.zero_le _)⟩

/-- `tuple_pair_projection_keeps_full_fst?/2` checks for a remaining tuple outside every negated pair. -/
theorem keeps_full (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {b : Term} (hb : TField E b) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2» (D m) (Term.list P) b = .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ w, denTF E den b w = Bool.true ∧
        ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → denTF E den nb w = Bool.false) := by
  obtain ⟨u, tu, su, run⟩ := union_pairs (den := den) P hP
  obtain ⟨d, rd, td, sd, -⟩ := tuple_diff_lh ef hb tu
  obtain ⟨e, re, se⟩ := tuple_empty_exact ef td []
  have se := se (lh d + 1) (by omega) (safeT_nil _)
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2», run m, rd, re m hm,
      Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [sd] at hw
      simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true'] at hw
      refine ⟨w, hw.1, fun p mp f nb e => ?_⟩
      cases h : denTF E den nb w
      · rfl
      · exact absurd ((su w).mpr ⟨p, mp, f, nb, e, h⟩) (by rw [hw.2]; simp)
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro w hw none
      have := (se.mp rfl) w
      rw [sd, hw] at this
      simp only [Bool.true_and, Bool.not_eq_false'] at this
      obtain ⟨p, mp, f, nb, e, h⟩ := (su w).mp this
      rw [none p mp f nb e] at h
      cases h

/-- Lists of pairs whose tuple types are not empty. -/
def QOk (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) : Prop :=
  ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ E f ∧ TField E b ∧ ∃ w, denTF E den b w = Bool.true

/-- A value and a remaining tuple of values in some pair. -/
def InPairs (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) (y : V) (w : List V) : Prop :=
  ∃ p ∈ Q, PairIn E den p y w

/-- Lists of pairs whose element types have values. -/
def QF (den : Term → V → Prop) (Q : List Term) : Prop := ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ ∃ y, den f y

theorem empty_bool (ef : EF nd E V den tl K) {a : Term} (ha : E a) {m : Nat} (hm : K ≤ m) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ v, ¬den a v) :=
  let ⟨b, run, sem⟩ := ef.empty_pub ha; ⟨b, run m hm, sem⟩

/-- `prepend_tuple_pair_unless_empty_diff/4` keeps the pair of the difference, unless it is empty. -/
theorem prepend_pair (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f nv b : Term} (hf : E f) (hnv : E nv)
    (hb : TField E b) (nb : ∃ w, denTF E den b w = Bool.true) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«prepend_tuple_pair_unless_empty_diff/4» (D m) f nv b (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ QOk E den new ∧
      (∀ y w, InPairs E den new y w ↔ (den f y ∧ ¬den nv y) ∧ denTF E den b w = Bool.true) ∧ QF den new := by
  obtain ⟨d, hd, rd, sd⟩ := ef.opt_diff [] hf hnv hm
  obtain ⟨e, re, se⟩ := empty_bool ef hd hm
  cases e
  · refine ⟨[.tuple #[d, b]], fun A => ?_, ?_, fun y w => ?_, fun p mp => ?_⟩
    · simp [Elixir.Module.Types.Descr.«prepend_tuple_pair_unless_empty_diff/4»,
        Elixir.Module.Types.Descr.«opt_difference/2», rd, re, Lynx.Term.isMember, Term.list]
    · intro p mp; simp at mp; subst mp; exact ⟨d, b, rfl, hd, hb, nb⟩
    · simp [InPairs, pairIn_iff, sd]
    · simp at mp; subst mp
      exact ⟨d, b, rfl, Classical.byContradiction fun none => by
        have := se.mpr fun v hv => none ⟨v, hv⟩
        cases this⟩
  · refine ⟨[], fun A => ?_, by simp [QOk], fun y w => ?_, by simp [QF]⟩
    · simp [Elixir.Module.Types.Descr.«prepend_tuple_pair_unless_empty_diff/4»,
        Elixir.Module.Types.Descr.«opt_difference/2», rd, re, Lynx.Term.isMember]
    · simp only [InPairs, List.not_mem_nil, false_and, exists_false, false_iff, not_and]
      intro h₁ _
      exact se.mp rfl y ((sd y).mpr h₁)

/-- One step of `tuple_project_negative_pairs/3`: a pair minus a negated pair, as pairs of non-empty tuple types. -/
theorem project_step (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {nv nb x : Term} (hnv : E nv)
    (hnb : TField E nb) (hx : QOk E den [x]) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4» (D m) nb nv x (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ QOk E den new ∧
      (∀ y w, InPairs E den new y w ↔ PairIn E den x y w ∧ ¬(den nv y ∧ denTF E den nb w = Bool.true)) ∧
        (QF den [x] → QF den new) := by
  obtain ⟨f, b, rfl, hf, hb, nbw⟩ := hx _ List.mem_cons_self
  obtain ⟨ib, rib, tib, sib, -⟩ := tuple_inter_lh (den := den) hb hnb
  obtain ⟨eib, reib, seib⟩ := tuple_empty_exact ef tib []
  have seib := seib (lh ib + 1) (by omega) (safeT_nil _)
  obtain ⟨i_f, hif, rif, sif⟩ := ef.opt_inter [] hf hnv (show K ≤ m by omega)
  obtain ⟨e1, re1, se1⟩ := empty_bool ef hif (show K ≤ m by omega)
  obtain ⟨db, rdb, tdb, sdb, -⟩ := tuple_diff_lh ef hb hnb
  obtain ⟨e2, re2, se2⟩ := tuple_empty_exact ef tdb []
  have se2 := se2 (lh db + 1) (by omega) (safeT_nil _)
  obtain ⟨pnew, rp, qp, sp, fp⟩ := prepend_pair ef (m := m) (by omega) hf hnv hb nbw
  have keepSem : ∀ y w, InPairs E den [.tuple #[f, b]] y w ↔ PairIn E den (.tuple #[f, b]) y w := fun y w => by
    simp [InPairs]
  by_cases keep : (∃ k r, nb = .tuple #[k, .atom "closed", r]) ∧ eib = Bool.true
  · obtain ⟨⟨k, r, rfl⟩, rfl⟩ := keep
    refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun y w => ?_, id⟩
    · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
      simp [rib, reib m hm, Lynx.Term.isMember, Term.list]
    · rw [keepSem, pairIn_iff]
      refine ⟨fun h => ⟨h, fun ⟨_, h'⟩ => ?_⟩, fun h => h.1⟩
      have := seib.mp rfl w
      rw [sib, h.2, h'] at this
      cases this
  -- The pair meets the negated pair: the intersection of the remaining tuples is not known to be empty.
  cases e1
  · cases e2
    · refine ⟨pnew ++ [.tuple #[i_f, db]], fun A => ?_, ?_, fun y w => ?_, fun _ p mp => ?_⟩
      · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
        have rp' := rp (.tuple #[i_f, db] :: A)
        simp only [Term.list] at rp'
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb,
            re2 m hm, rp']
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb, re2 m hm, rp']
      · intro p mp
        rcases List.mem_append.mp mp with mp | mp
        · exact qp p mp
        · simp at mp; subst mp
          refine ⟨i_f, db, rfl, hif, tdb, ?_⟩
          exact Classical.byContradiction fun none => by
            have := se2.mpr fun v => by
              cases h : denTF E den db v
              · rfl
              · exact absurd ⟨v, h⟩ none
            cases this
      · simp only [InPairs, List.mem_append, List.mem_singleton] at sp ⊢
        rw [pairIn_iff]
        constructor
        · rintro ⟨p, mp | rfl, hp⟩
          · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (sp y w).mp ⟨p, mp, hp⟩
            exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
          · rw [pairIn_iff, sif, sdb] at hp
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
            refine ⟨⟨hp.1.1, hp.2.1⟩, fun h => ?_⟩
            rw [h.2] at hp; cases hp.2.2
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩
          by_cases hn : den nv y
          · refine ⟨_, Or.inr rfl, ?_⟩
            rw [pairIn_iff, sif, sdb, h₂]
            cases h : denTF E den nb w
            · exact ⟨⟨h₁, hn⟩, rfl⟩
            · exact absurd ⟨hn, h⟩ h₃
          · obtain ⟨p, mp, hp⟩ := (sp y w).mpr ⟨⟨h₁, hn⟩, h₂⟩
            exact ⟨p, Or.inl mp, hp⟩
      · rcases List.mem_append.mp mp with mp | mp
        · exact fp p mp
        · simp at mp; subst mp
          exact ⟨i_f, db, rfl, Classical.byContradiction fun none => by
            have := se1.mpr fun v hv => none ⟨v, hv⟩
            cases this⟩
    · refine ⟨pnew, fun A => ?_, qp, fun y w => ?_, fun _ => fp⟩
      · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb, re2 m hm, rp A]
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb, re2 m hm, rp A]
      · rw [sp, pairIn_iff]
        have cover : ∀ w, denTF E den b w = Bool.true → denTF E den nb w = Bool.true := fun w h => by
          have := se2.mp rfl w
          rw [sdb, h] at this
          simpa using this
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, fun hn => h₃ ⟨hn, cover w h₂⟩⟩, h₂⟩
  · refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun y w => ?_, id⟩
    · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
      by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
      · obtain ⟨k, r, rfl⟩ := hc
        have : eib = Bool.false := by
          cases eib
          · rfl
          · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
        subst this
        simp [rib, reib m hm, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, Term.list]
      · simp only
        split
        · exact absurd ⟨_, _, rfl⟩ hc
        · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, Term.list]
    · rw [keepSem, pairIn_iff]
      refine ⟨fun h => ⟨h, fun h' => (se1.mp rfl) y ((sif y).mpr ⟨h.1, h'.1⟩)⟩, fun h => h.1⟩

/-- `tuple_project_negative_pairs/3` splits a pair minus negated pairs into pairs of non-empty tuple types. -/
theorem project_pairs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {value rest : Term} (hv : E value) (hr : TField E rest) (nr : ∃ w, denTF E den rest w = Bool.true) :
    ∃ Q, Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» (D (n + 2)) (Term.list P) value rest =
        .ok (Term.list Q) ∧ QOk E den Q ∧
      (∀ y w, InPairs E den Q y w ↔ den value y ∧ denTF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬PairIn E den p y w) ∧
        ((∃ y, den value y) → QF den Q) := by
  obtain ⟨r, ⟨Q, rfl, qQ, sQ, fQ⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr"
    "-tuple_project_negative_pairs/3-fun-1-" #[]
    (fun pre a => ∃ Q, a = Term.list Q ∧ QOk E den Q ∧ (∀ y w, InPairs E den Q y w ↔
      den value y ∧ denTF E den rest w = Bool.true ∧ ∀ p ∈ pre, ¬PairIn E den p y w) ∧
      ((∃ y, den value y) → QF den Q)) P
    (fun pre x a mx ⟨Q, ea, qQ, sQ, fQ⟩ => by
      subst ea
      obtain ⟨nv, nb, rfl, hnv, hnb⟩ := hP x mx
      have each : ∀ p ∈ Q, ∃ new, (∀ A, Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (new ++ A))) ∧ QOk E den new ∧
          (∀ y w, InPairs E den new y w ↔ PairIn E den p y w ∧ ¬(den nv y ∧ denTF E den nb w = Bool.true)) ∧
          (QF den [p] → QF den new) :=
        fun p mp => project_step ef hn hnv hnb fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact qQ p mp
      classical
      let h : Term → List Term := fun p => if hp : p ∈ Q then Classical.choose (each p hp) else []
      have hh : ∀ p ∈ Q, (∀ A, Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (h p ++ A))) ∧ QOk E den (h p) ∧
          (∀ y w, InPairs E den (h p) y w ↔ PairIn E den p y w ∧ ¬(den nv y ∧ denTF E den nb w = Bool.true)) ∧
          (QF den [p] → QF den (h p)) := by
        intro p mp
        simp only [h, dite_eq_left mp]
        exact Classical.choose_spec (each p mp)
      have inner := foldl_lists_at (m := n + 1) "Elixir.Module.Types.Descr" "-tuple_project_negative_pairs/3-fun-0-"
        #[nb, nv] h Q (fun p mp A => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_project_negative_pairs/3-fun-0-/2».pure]
          exact (hh p mp).1 A) []
      refine ⟨Term.list (Q.reverse.flatMap h), ⟨Q.reverse.flatMap h, rfl, fun p mp => ?_, fun y w => ?_, fun nv p mp => ?_⟩,
        ?_⟩
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.1 p mp
      · simp only [InPairs, List.mem_flatMap, List.mem_reverse, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨p, ⟨q, mq, mp⟩, hp⟩
          obtain ⟨hq, hn'⟩ := ((hh q mq).2.2.1 y w).mp ⟨p, mp, hp⟩
          obtain ⟨h₁, h₂, h₃⟩ := (sQ y w).mp ⟨q, mq, hq⟩
          refine ⟨h₁, h₂, fun p' mp' hp' => ?_⟩
          rcases mp' with mp' | rfl
          · exact h₃ p' mp' hp'
          · exact hn' (pairIn_iff.mp hp')
        · rintro ⟨h₁, h₂, h₃⟩
          obtain ⟨q, mq, hq⟩ := (sQ y w).mpr ⟨h₁, h₂, fun p' mp' => h₃ p' (Or.inl mp')⟩
          obtain ⟨p, mp, hp⟩ := ((hh q mq).2.2.1 y w).mpr ⟨hq, fun h => h₃ _ (Or.inr rfl) (pairIn_iff.mpr h)⟩
          exact ⟨p, ⟨q, mq, mp⟩, hp⟩
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.2.2 (fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact fQ nv q mq) p mp
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_project_negative_pairs/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-1-/2»] using inner)
    (Term.list [.tuple #[value, rest]]) ⟨[.tuple #[value, rest]], rfl, fun p mp => by
      simp at mp; subst mp; exact ⟨value, rest, rfl, hv, hr, nr⟩, fun y w => by simp [InPairs, pairIn_iff],
      fun ⟨y, hy⟩ p mp => by simp at mp; subst mp; exact ⟨value, rest, rfl, y, hy⟩⟩
  exact ⟨Q, by simpa [Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3»] using run, qQ, sQ, fQ⟩

/-- The final fold of `tuple_bdd_fetch_lines/3` unites the element types of the pairs. -/
theorem union_fields (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (Q : List Term)
    (hQ : ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ E f) :
    ∃ u, E u ∧ Erlang.lists.«foldl/3» (D (n + 1)) (.function "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[])
        (.map []) (Term.list Q) = .ok u ∧
      ∀ y, den u y ↔ ∃ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ den f y := by
  obtain ⟨u, ⟨hu, su⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ den f y) Q
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨f, b, rfl, hf⟩ := hQ x mx
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hf ha hn
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_fetch_lines/3-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_bdd_fetch_lines/3-fun-0-/2», Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  exact ⟨u, hu, run, su⟩

/-- The element type a line with negations projects to: the values of its pair outside the negated pairs. -/
theorem proj_value (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {value rest : Term} (hv : E value) (hr : TField E rest) (nr : ∃ w, denTF E den rest w = Bool.true) :
    ∃ (s : Bool) (value' : Term), Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2» (D (n + 2)) (Term.list P) rest =
        .ok (boolAtom s) ∧ (s = Bool.true → value' = value) ∧
      (s = Bool.false → ∃ Q, Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» (D (n + 2)) (Term.list P) value rest =
        .ok (Term.list Q) ∧ Erlang.lists.«foldl/3» (D (n + 2))
          (.function "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[]) (.map []) (Term.list Q) =
            .ok value') ∧ E value' ∧
      ∀ y, den value' y ↔ ∃ w, den value y ∧ denTF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬PairIn E den p y w := by
  obtain ⟨s, rs, ss⟩ := keeps_full (den := den) ef (m := n + 2) (by omega) P hP hr
  cases s
  · obtain ⟨Q, rQ, qQ, sQ, -⟩ := project_pairs ef hn P hP hv hr nr
    obtain ⟨u, hu, ru, su⟩ := union_fields ef (n := n + 1) (by omega) Q fun p mp => by
      obtain ⟨f, b, e, hf, -⟩ := qQ p mp
      exact ⟨f, b, e, hf⟩
    refine ⟨Bool.false, u, rs, by simp, fun _ => ⟨Q, rQ, ru⟩, hu, fun y => ?_⟩
    rw [su]
    constructor
    · rintro ⟨p, mp, f, b, rfl, hy⟩
      obtain ⟨f', b', e, -, -, w, hw⟩ := qQ _ mp
      simp only [Term.tuple.injEq] at e
      obtain ⟨rfl, rfl, -⟩ := e
      exact ⟨w, (sQ y w).mp ⟨_, mp, pairIn_iff.mpr ⟨hy, hw⟩⟩⟩
    · rintro ⟨w, h⟩
      obtain ⟨p, mp, hp⟩ := (sQ y w).mpr h
      obtain ⟨f, b, rfl, hy, -⟩ := hp
      exact ⟨_, mp, f, b, rfl, hy⟩
  · obtain ⟨w₀, hw₀, out⟩ := ss.mp rfl
    refine ⟨Bool.true, value, rs, fun _ => rfl, by simp, hv, fun y => ⟨fun hy => ⟨w₀, hy, hw₀, fun p mp hp => ?_⟩,
      fun ⟨_, hy, _⟩ => hy⟩⟩
    obtain ⟨f, nb, rfl, -, hnb⟩ := hp
    rw [out _ mp f nb rfl] at hnb
    cases hnb

end

end Elixir.STTDescrProofsTest.Nest
