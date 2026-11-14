namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Inserting elements into tuple types. -/

theorem split3_list : ∀ (l acc : List Term) (i : Nat), i ≤ l.length →
    Erlang.lists.«split/3» (.integer i) (Term.list l) (Term.list acc) =
      .ok (.tuple #[Term.list (acc.reverse ++ l.take i), Term.list (l.drop i)])
  | l, acc, 0, _ => by
    have := reverse_list acc []
    rw [Erlang.lists.«split/3».eq_def]
    simp only [List.append_nil] at this
    simp [Term.list] at this
    simp [this]
  | [], _, _ + 1, h => by simp at h
  | x :: l, acc, j + 1, h => by
    have ih := split3_list l (x :: acc) j (by simp at h; omega)
    rw [Erlang.lists.«split/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp [Erlang.erlang.«-/2_integers», ih]

theorem split3_short : ∀ (l acc : List Term) (i : Nat), l.length < i →
    Erlang.lists.«split/3» (.integer i) (Term.list l) (Term.list acc) = .ok (.atom "badarg")
  | _, _, 0, h => by simp at h
  | [], acc, j + 1, _ => by
    have ne : ¬((j : Int) + 1 = 0) := by omega
    rw [Erlang.lists.«split/3».eq_def]
    split <;> simp_all [Term.list]
  | x :: l, acc, j + 1, h => by
    have ih := split3_short l (x :: acc) j (by simp at h; omega)
    rw [Erlang.lists.«split/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp [Erlang.erlang.«-/2_integers», ih]

theorem is_list_l (l : List Term) : Erlang.erlang.«is_list/1» (Term.list l) = .ok (.atom "true") := by
  cases l <;> rfl

theorem split_list (l : List Term) (i : Nat) (h : i ≤ l.length) :
    Erlang.lists.«split/2» (.integer i) (Term.list l) = .ok (.tuple #[Term.list (l.take i), Term.list (l.drop i)]) := by
  have := split3_list l [] i h
  simp only [List.reverse_nil, List.nil_append] at this
  simp [Erlang.lists.«split/2», Erlang.erlang.«>=/2», Int.isGE_compare,
    is_list_l, Erlang.erlang.«and/2», this]

theorem split_short (l : List Term) (i : Nat) (h : l.length < i) (r : Term) :
    Erlang.lists.«split/2» (.integer i) (Term.list l) ≠ .ok r := by
  have := split3_short l [] i h
  simp [Erlang.lists.«split/2», Erlang.erlang.«>=/2», Int.isGE_compare,
    is_list_l, Erlang.erlang.«and/2», this, Erlang.erlang.«error/2»]

/-- The elements of a literal an element is inserted into: open literals are filled with top types up to the index. -/
def fillT (tag : String) (l : List Term) (i : Nat) : List Term :=
  if tag = "open" ∧ l.length < i then l ++ List.replicate (i - l.length) (.atom "term") else l

/-- The elements of a literal with an element inserted at an index. -/
def insL (tag : String) (l : List Term) (i : Nat) (x : Term) : List Term :=
  (fillT tag l i).take i ++ x :: (fillT tag l i).drop i

theorem fillT_len {tag : String} {l : List Term} {i : Nat} (fits : tag = "open" ∨ i ≤ l.length) :
    i ≤ (fillT tag l i).length := by
  unfold fillT
  split
  · simp only [List.length_append, List.length_replicate]; omega
  · rcases fits with rfl | h
    · simp_all
    · exact h

/-- `tuple_insert_leaf/4` inserts an element into a literal, unless the literal is closed and too short. -/
theorem insert_leaf_run {tag : String} (g : tag = "open" ∨ tag = "closed") (l : List Term) (i : Nat) (x : Term) :
    (tag = "closed" ∧ l.length < i ∧ ∀ r, Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l)
        (.integer i) x ≠ .ok r) ∨
      ((tag = "open" ∨ i ≤ l.length) ∧ ∃ k : Int, Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l)
        (.integer i) x = .ok (.tuple #[.integer k, .atom tag, Term.list (insL tag l i x)]) ∧
        KeyOk (.tuple #[.integer k, .atom tag, Term.list (insL tag l i x)])) := by
  obtain ⟨k, run, key⟩ := leaf_new_key tag g (insL tag l i x)
  rcases g with rfl | rfl
  · right
    refine ⟨Or.inl rfl, k, ?_, key⟩
    by_cases short : l.length < i
    · have fill := fill_list l i (by omega)
      have sp := split_list (l ++ List.replicate (i - l.length) (.atom "term")) i (by simp; omega)
      have e : fillT "open" l i = l ++ List.replicate (i - l.length) (.atom "term") := by simp [fillT, short]
      rw [insL, e] at run
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, length_list, Erlang.erlang.«</2»,
        Int.compare_eq_lt, short, fill, sp, ← list_cons, Erlang.erlang.«==/2», insL, e]
      rw [append_list, Lynx.Except.ok_bind, run]
    · have sp := split_list l i (by omega)
      have e : fillT "open" l i = l := by simp [fillT, short]
      rw [insL, e] at run
      have nlt : ¬(l.length : Int) < i := by omega
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, length_list, Erlang.erlang.«</2»,
        Int.compare_eq_lt, nlt, sp, ← list_cons, Erlang.erlang.«==/2», insL, e]
      rw [append_list, Lynx.Except.ok_bind, run]
  · have e : fillT "closed" l i = l := by simp [fillT]
    by_cases short : l.length < i
    · left
      refine ⟨rfl, short, fun r h => ?_⟩
      simp only [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, Erlang.erlang.«==/2»] at h
      simp at h
      cases hs : Erlang.lists.«split/2» (.integer i) (Term.list l) with
      | error _ => simp [hs] at h
      | ok s => exact split_short l i short s hs
    · right
      have sp := split_list l i (by omega)
      rw [insL, e] at run
      refine ⟨Or.inr (by omega), k, ?_, key⟩
      simp [Elixir.Module.Types.Descr.«tuple_insert_leaf/4», Lynx.Except.andAlso, sp, ← list_cons,
        Erlang.erlang.«==/2», insL, e]
      rw [append_list, Lynx.Except.ok_bind, run]

section
variable {V : Type} {den : Term → V → Prop}

/-- Tuples of values with a value inserted at an index. -/
def Ins (P : List V → Prop) (i : Nat) (Q : V → Prop) (w : List V) : Prop :=
  ∃ w₁ y w₂, w = w₁ ++ y :: w₂ ∧ w₁.length = i ∧ Q y ∧ P (w₁ ++ w₂)

theorem ins_or {P P' : List V → Prop} {i : Nat} {Q : V → Prop} {w : List V} :
    Ins (fun u => P u ∨ P' u) i Q w ↔ Ins P i Q w ∨ Ins P' i Q w := by
  constructor
  · rintro ⟨w₁, y, w₂, e, len, hy, h | h⟩
    · exact Or.inl ⟨w₁, y, w₂, e, len, hy, h⟩
    · exact Or.inr ⟨w₁, y, w₂, e, len, hy, h⟩
  · rintro (⟨w₁, y, w₂, e, len, hy, h⟩ | ⟨w₁, y, w₂, e, len, hy, h⟩)
    · exact ⟨w₁, y, w₂, e, len, hy, Or.inl h⟩
    · exact ⟨w₁, y, w₂, e, len, hy, Or.inr h⟩

theorem ins_congr {P P' : List V → Prop} {i : Nat} {Q : V → Prop} {w : List V} (h : ∀ u, P u ↔ P' u) :
    Ins P i Q w ↔ Ins P' i Q w := by
  simp only [Ins, h]

/-- The values of a literal with an element inserted. -/
theorem inT_insL (hterm : ∀ y, den (.atom "term") y) {tag : String} (l : List Term) (i : Nat) (x : Term)
    (fits : tag = "open" ∨ i ≤ l.length) (w : List V) :
    InT den (tag == "closed") (insL tag l i x) w ↔ Ins (InT den (tag == "closed") l) i (den x) w := by
  have hL := fillT_len (l := l) fits
  have same : ∀ u : List V, i ≤ u.length → (InT den (tag == "closed") (fillT tag l i) u ↔ InT den (tag == "closed") l u) := by
    intro u lu
    unfold fillT
    split
    · rename_i h
      obtain ⟨rfl, short⟩ := h
      simp only [show ("open" == "closed") = Bool.false from rfl]
      exact ⟨fun h => (InT.fill_open h).1, fun h => inT_fill_open _ h (by omega) hterm⟩
    · exact Iff.rfl
  have sp : fillT tag l i = (fillT tag l i).take i ++ (fillT tag l i).drop i := (List.take_append_drop _ _).symm
  have lt : ((fillT tag l i).take i).length = i := by simp; omega
  constructor
  · intro h
    have len := h.length_le
    simp only [insL, List.length_append, List.length_cons] at len
    obtain ⟨w₁, y, w₂, rfl, l₁⟩ : ∃ w₁ y w₂, w = w₁ ++ y :: w₂ ∧ w₁.length = i :=
      ⟨w.take i, w[i]'(by omega), w.drop (i + 1), by simp, by simp; omega⟩
    rw [insL, InT.split _ x _ w₁ y w₂ (by omega), ← sp] at h
    exact ⟨w₁, y, w₂, rfl, l₁, h.1, (same _ (by simp; omega)).mp h.2⟩
  · rintro ⟨w₁, y, w₂, rfl, l₁, hy, h⟩
    rw [insL, InT.split _ x _ w₁ y w₂ (by omega), ← sp]
    exact ⟨hy, (same _ (by simp; omega)).mpr h⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem insL_els {tag : String} {l : List Term} {i : Nat} {x : Term} (ef : EF nd E V den tl K) (hl : ∀ e ∈ l, E e)
    (hx : E x) : ∀ e ∈ insL tag l i x, E e := by
  have hf : ∀ e ∈ fillT tag l i, E e := by
    intro e me
    unfold fillT at me
    split at me
    · rcases List.mem_append.mp me with me | me
      · exact hl e me
      · rw [List.eq_of_mem_replicate me]; exact ef.term
    · exact hl e me
  intro e me
  rcases List.mem_append.mp me with me | me
  · exact hf e (List.mem_of_mem_take me)
  · rcases List.mem_cons.mp me with rfl | me
    · exact hx
    · exact hf e (List.mem_of_mem_drop me)

/-- An inserted literal, as a tuple field, with the values of the literal with a value inserted. -/
theorem insert_leaf (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) {x : Term} (hx : E x) (i : Nat) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x = .ok r) :
    TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ Ins (InT den (tag == "closed") l) i (den x) w := by
  rcases insert_leaf_run g l i x with ⟨-, -, none⟩ | ⟨fits, k, run', key⟩
  · exact absurd run (none r)
  rw [run'] at run
  cases run
  have hl' := insL_els (i := i) (x := x) (tag := tag) ef hl hx
  refine ⟨tleaf_field g hl' key, fun w => ?_⟩
  rw [denTF_leaf ef g hl', vT_lit ef g hl']
  exact inT_insL ef.den_term l i x fits w

/-- `tuple_insert_leaves/4` inserts an element into the literals of a union of literals, and fails on other BDDs. -/
theorem insert_leaves (ef : EF nd E V den tl K) {x : Term} (hx : E x) (i : Nat) :
    ∀ (ok : Term → Prop) (r : Term), Bdd ok r → (∀ t, ok t → TupleLit E t) → ∀ (acc res : Term), TField E acc →
      Elixir.Module.Types.Descr.«tuple_insert_leaves/4» r (.integer i) x acc = .ok res →
      TField E res ∧ ∀ w, denTF E den res w = Bool.true ↔
        denTF E den acc w = Bool.true ∨ Ins (fun u => eval (valT E den u) r = Bool.true) i (den x) w := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit E t) → ∀ (acc res : Term), TField E acc →
      Elixir.Module.Types.Descr.«tuple_insert_leaves/4» r (.integer i) x acc = .ok res →
      TField E res ∧ ∀ w, denTF E den res w = Bool.true ↔
        denTF E den acc w = Bool.true ∨ Ins (fun u => eval (valT E den u) r = Bool.true) i (den x) w) ?_ ?_ ?_ ?_
  · intro ok _ acc res _ run
    simp [Elixir.Module.Types.Descr.«tuple_insert_leaves/4»] at run
  · intro ok _ acc res ha run
    simp only [Elixir.Module.Types.Descr.«tuple_insert_leaves/4», pure, Except.pure, Except.ok.injEq] at run
    subst run
    refine ⟨ha, fun w => ?_⟩
    simp [Ins]
  · intro ok k a b okl okLit acc res ha run
    obtain ⟨k', tag, l, e, g, hl⟩ := okLit _ okl
    rw [e] at run ⊢
    simp only [Elixir.Module.Types.Descr.«tuple_insert_leaves/4»] at run
    cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x with
    | error _ => simp [hr] at run
    | ok r =>
      rw [hr, Lynx.Except.ok_bind] at run
      obtain ⟨fr, sr⟩ := insert_leaf (den := den) ef g hl hx i hr
      obtain ⟨u, ru, tu, su, -⟩ := tuple_union_lh (den := den) fr ha
      rw [ru] at run
      cases run
      refine ⟨tu, fun w => ?_⟩
      rw [su, Bool.or_eq_true, sr, or_comm]
      refine or_congr Iff.rfl (ins_congr fun u => ?_)
      rw [eval_leaf, vT_lit ef g hl]
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc res ha run
    have okLit' : ∀ t, Above ok lit t → TupleLit E t := fun t ht => okLit t ht.1
    obtain ⟨k', tag, l, rfl, g, hl⟩ := okLit _ okl
    by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
    · obtain ⟨rfl, rfl⟩ := shape
      simp only [Elixir.Module.Types.Descr.«tuple_insert_leaves/4»] at run
      cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x with
      | error _ => simp [hr] at run
      | ok r =>
        rw [hr, Lynx.Except.ok_bind] at run
        obtain ⟨fr, sr⟩ := insert_leaf (den := den) ef g hl hx i hr
        obtain ⟨a, ra, ta, sa, -⟩ := tuple_union_lh (den := den) fr ha
        rw [ra, Lynx.Except.ok_bind] at run
        obtain ⟨tres, sres⟩ := iu okLit' a res ta run
        refine ⟨tres, fun w => ?_⟩
        rw [sres, sa, Bool.or_eq_true, sr]
        have ev : ∀ v : List V, eval (valT E den v) (.tuple #[.integer h, .tuple #[.integer k', .atom tag, Term.list l],
            .atom "bdd_top", u, .atom "bdd_bot"]) = Bool.true ↔
            InT den (tag == "closed") l v ∨ eval (valT E den v) u = Bool.true := fun v => by
          simp [eval, vT_lit ef g hl]
        rw [ins_congr ev, ins_or, or_assoc]
        exact or_left_comm
    · exfalso
      rw [Elixir.Module.Types.Descr.«tuple_insert_leaves/4».eq_def] at run
      split at run
      all_goals first
        | (rename_i heq; simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at heq; simp_all; done)
        | (simp_all; done)
        | skip

end

end Elixir.STTDescrProofsTest.Nest
