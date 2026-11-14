namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple types as unions of literals without negations. -/

/-- `dedup_contiguous/1` keeps elements of a list, and one equal to each of them. -/
theorem dedup_run : ∀ (n : Nat) (l : List Term), l.length ≤ n → ∃ l',
    Elixir.Module.Types.Descr.«dedup_contiguous/1» (Term.list l) = .ok (Term.list l') ∧ (∀ y ∈ l', y ∈ l) ∧
      ∀ x ∈ l, ∃ y ∈ l', compare (fuel x y) x y = .eq
  | _, [], _ => ⟨[], by rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]; rfl, by simp, by simp⟩
  | n, [x], _ => by
    refine ⟨[x], ?_, by simp, by simp [compare_self]⟩
    rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
    simp only [Term.list]
    rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
    rfl
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, x :: y :: rest, h => by
    by_cases same : compareExact (fuel y x) y x = .eq
    · obtain ⟨l', run, sub, cover⟩ := dedup_run n (x :: rest) (by simp at h ⊢; omega)
      refine ⟨l', ?_, fun z mz => ?_, fun z mz => ?_⟩
      · rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
        simp only [Term.list] at run ⊢
        simp [Erlang.erlang.«=:=/2», same, run]
      · rcases List.mem_cons.mp (sub z mz) with rfl | mz'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mz')
      · rcases List.mem_cons.mp mz with rfl | mz
        · exact cover z List.mem_cons_self
        rcases List.mem_cons.mp mz with rfl | mz
        · obtain ⟨w, mw, cw⟩ := cover x List.mem_cons_self
          exact ⟨w, mw, Lynx.Term.compare_eq_trans (compare_eq_of_compareExact_eq _ _ same) cw⟩
        · exact cover z (List.mem_cons_of_mem _ mz)
    · obtain ⟨l', run, sub, cover⟩ := dedup_run n (y :: rest) (by simp at h ⊢; omega)
      refine ⟨x :: l', ?_, fun z mz => ?_, fun z mz => ?_⟩
      · rw [Elixir.Module.Types.Descr.«dedup_contiguous/1».eq_def]
        simp only [Term.list] at run ⊢
        simp [Erlang.erlang.«=:=/2», same, run]
      · rcases List.mem_cons.mp mz with rfl | mz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (sub z mz)
      · rcases List.mem_cons.mp mz with rfl | mz
        · exact ⟨z, List.mem_cons_self, compare_self z⟩
        · obtain ⟨w, mw, cw⟩ := cover z mz
          exact ⟨w, List.mem_cons_of_mem _ mw, cw⟩

/-- `lists:flatmap/2` with steps that return lists. -/
theorem flatmap1_lists {m : Nat} (f : Term) (h : Term → List Term) :
    ∀ l : List Term, (∀ x ∈ l, (D m).pure f #[x] = .ok (Term.list (h x))) →
      Erlang.lists.«flatmap_1/2» (D m) f (Term.list l) = .ok (Term.list (l.flatMap h)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«flatmap_1/2»]
  | cons x xs ih =>
    intro step
    have tail := ih (fun y my => step y (List.mem_cons_of_mem _ my))
    rw [Erlang.lists.«flatmap_1/2».eq_def]
    simp only at tail ⊢
    simp only [step x List.mem_cons_self, Lynx.Except.ok_bind, List.flatMap_cons]
    rcases hx : h x with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simpa [Term.list] using tail
    · simp [Term.list, tail]
    · have := append_list (a :: b :: r) (xs.flatMap h)
      simp only [Term.list] at this
      simp [Term.list, tail, this]

theorem flatmap_lists {m : Nat} (mo nm : String) (caps : Array Term) (h : Term → List Term) (l : List Term)
    (step : ∀ x ∈ l, (D m).pure (.function mo nm 1 caps) #[x] = .ok (Term.list (h x))) :
    Erlang.lists.«flatmap/2» (D m) (.function mo nm 1 caps) (Term.list l) = .ok (Term.list (l.flatMap h)) := by
  have := flatmap1_lists (.function mo nm 1 caps) h l step
  simp [Erlang.lists.«flatmap/2», Erlang.erlang.«is_function/2», this]

/-- Folds whose steps may fail, keeping a relation when they succeed. -/
theorem foldl1_ok {m : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a a', x ∈ l → R pre a → (D m).pure f #[x, a] = .ok a' → R (pre ++ [x]) a') :
    ∀ (rest pre : List Term) acc r, (∀ x ∈ rest, x ∈ l) → R pre acc →
      Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r → R (pre ++ rest) r := by
  intro rest
  induction rest with
  | nil =>
    intro pre acc r _ h run
    simp [Erlang.lists.«foldl_1/3», pure, Except.pure] at run
    subst run; simpa using h
  | cons x xs ih =>
    intro pre acc r sub h run
    rw [Erlang.lists.«foldl_1/3».eq_def] at run
    simp only at run ih
    cases hs : (D m).pure f #[x, acc] with
    | error _ => rw [hs] at run; cases run
    | ok a' =>
      rw [hs, Lynx.Except.ok_bind] at run
      have := ih (pre ++ [x]) a' r (fun y my => sub y (List.mem_cons_of_mem _ my))
        (step pre x acc a' (sub x List.mem_cons_self) h hs) run
      simpa using this

theorem foldl_ok {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a a', x ∈ l → R pre a → (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a' → R (pre ++ [x]) a')
    (acc : Term) (h : R [] acc) (r : Term)
    (run : Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r) : R l r := by
  have := foldl1_ok (.function mo nm 2 caps) R l step l [] acc r (fun _ h => h) h
  simp only [List.nil_append] at this
  apply this
  cases l with
  | nil => simpa [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list, Erlang.lists.«foldl_1/3»] using run
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only [Term.list] at run ⊢
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2»] using run

section
variable {E : Term → Prop} {V : Type} {den : Term → V → Prop}

/-- Literals without negations or keys: a tag and element types. -/
def Piece (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, E e

/-- Tuples of values in a literal without negations. -/
def PieceIn (den : Term → V → Prop) (p : Term) (w : List V) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ InT den (tag == "closed") l w

theorem pieceIn_iff {tag : String} {l : List Term} {w : List V} :
    PieceIn den (.tuple #[.atom tag, Term.list l]) w ↔ InT den (tag == "closed") l w := by
  constructor
  · rintro ⟨tag', l', e, h⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Term.atom.injEq, and_true] at e
    obtain ⟨rfl, e⟩ := e
    rwa [list_inj e]
  · intro h; exact ⟨tag, l, rfl, h⟩

/-- Literals without negations equal up to comparison hold the same tuples. -/
theorem pieceIn_congr {K : Nat} {Safe : List (Term × Term) → Prop} (sem : ElemSem E K V den Safe) {p q : Term}
    (hp : Piece E p) (hq : Piece E q) (c : compare (fuel p q) p q = .eq) {w : List V} (h : PieceIn den q w) : PieceIn den p w := by
  obtain ⟨t₁, l₁, rfl, -, h₁⟩ := hp
  obtain ⟨t₂, l₂, rfl, -, h₂⟩ := hq
  rw [compare_tuple] at c
  simp [List.compareLex] at c
  split at c <;> try cases c
  rename_i e₁
  split at c <;> try cases c
  rename_i e₂
  have t : t₁ = t₂ := by have := (compare_eq_atom (.atom t₁) t₂).mp e₁; simpa using this
  subst t
  rw [pieceIn_iff] at h ⊢
  exact list_compare_inT sem h₁ h₂ e₂ h

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Tuples of values outside element types at some position of both. -/
def Differs (den : Term → V → Prop) : List Term → List V → Prop
  | n :: ns, y :: u => ¬den n y ∨ Differs den ns u
  | _, _ => False

/-- The tuples of a literal: long enough, nowhere outside its elements, and of its size when closed. -/
theorem inT_iff_differs {c : Bool} : ∀ (l : List Term) (w : List V),
    InT den c l w ↔ l.length ≤ w.length ∧ ¬Differs den l w ∧ (c = Bool.true → w.length = l.length)
  | [], [] => by simp [InT, Differs]
  | [], _ :: _ => by cases c <;> simp [InT, Differs]
  | _ :: _, [] => by simp [InT]
  | e :: l, y :: w => by
    have ih := inT_iff_differs (c := c) l w
    simp only [InT, Differs, List.length_cons, ih, not_or, Classical.not_not]
    constructor
    · rintro ⟨hy, a, b, c'⟩; exact ⟨by omega, ⟨hy, b⟩, fun h => by rw [c' h]⟩
    · rintro ⟨a, ⟨hy, b⟩, c'⟩; exact ⟨hy, by omega, b, fun h => by have := c' h; omega⟩

theorem inT_last {x : Term} : ∀ (A : List Term) (v : List V),
    InT den Bool.true (A ++ [x]) v ↔ ∃ v₁ y, v = v₁ ++ [y] ∧ InT den Bool.true A v₁ ∧ den x y := by
  intro A v
  rw [InT.mid]
  constructor
  · rintro ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩
    have : v₂ = [] := by cases v₂ <;> simp_all [InT]
    subst this
    exact ⟨v₁, y, rfl, h₁, hy⟩
  · rintro ⟨v₁, y, rfl, h₁, hy⟩
    exact ⟨v₁, y, [], rfl, h₁, hy, trivial⟩

/-- `zip_empty_intersection?/2` finds a position where two literals have disjoint elements. -/
theorem zip_empty_run (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) :
    ∀ (l₁ l₂ : List Term), (∀ e ∈ l₁, E e) → (∀ e ∈ l₂, E e) → ∃ b : Bool,
      Elixir.Module.Types.Descr.«zip_empty_intersection?/2» (D m) (Term.list l₁) (Term.list l₂) = .ok (boolAtom b) ∧
      (b = Bool.true → ∀ w, InT den Bool.false l₁ w → InT den Bool.false l₂ w → False)
  | [], l₂, _, _ => ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«zip_empty_intersection?/2», boolAtom], by simp⟩
  | x :: l₁, [], _, _ => ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«zip_empty_intersection?/2», boolAtom],
      by simp⟩
  | x :: l₁, y :: l₂, h₁, h₂ => by
    obtain ⟨c, hc, rc, sc, -⟩ := ef.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
    obtain ⟨e, re, se⟩ := empty_bool ef hc hm
    cases e
    · obtain ⟨b, rb, sb⟩ := zip_empty_run ef hm l₁ l₂ (fun e me => h₁ e (List.mem_cons_of_mem _ me))
        (fun e me => h₂ e (List.mem_cons_of_mem _ me))
      refine ⟨b, ?_, fun hb w i₁ i₂ => ?_⟩
      · rw [Elixir.Module.Types.Descr.«zip_empty_intersection?/2».eq_def]
        simp only at rb ⊢
        simp [rc m hm, re, rb, boolAtom]
      · cases w with
        | nil => exact i₁
        | cons z w => exact sb hb w i₁.2 i₂.2
    · refine ⟨Bool.true, ?_, fun _ w i₁ i₂ => ?_⟩
      · rw [Elixir.Module.Types.Descr.«zip_empty_intersection?/2».eq_def]
        simp [rc m hm, re, boolAtom]
      · cases w with
        | nil => exact i₁
        | cons z w => exact se.mp rfl z ((sc z).mpr ⟨i₁.1, i₂.1⟩)

theorem content_nil (d : Dispatcher) (acc tag neg nl : Term) :
    Elixir.Module.Types.Descr.«tuple_elim_content/4» d acc tag .nil (.cons neg nl) =
      Elixir.Module.Types.Descr.«tuple_elim_content/4» d acc tag (Term.list [.atom "term"]) (.cons neg nl) := by
  rw [Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]
  conv => rhs; rw [Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]

/-- `tuple_elim_content/4` splits the tuples of a literal outside a negated one at the first position outside it. -/
theorem elim_content (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag : String} (g : tag = "open" ∨ tag = "closed") :
    ∀ (nl acc l : List Term), (∀ e ∈ nl, E e) → (∀ e ∈ acc, E e) → (∀ e ∈ l, E e) →
      (tag = "closed" → nl.length ≤ l.length) →
      ∃ P, Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m) (Term.list acc) (.atom tag) (Term.list l) (Term.list nl) =
          .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
        ∀ w, (∃ p ∈ P, PieceIn den p w) ↔
          ∃ v₁ u, w = v₁ ++ u ∧ InT den Bool.true acc.reverse v₁ ∧ InT den (tag == "closed") l u ∧ Differs den nl u := by
  intro nl
  induction nl with
  | nil =>
    intro acc l _ _ _ _
    refine ⟨[], ?_, by simp, fun w => by simp [Differs]⟩
    rw [Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]
    rfl
  | cons neg nl ih =>
    intro acc l hnl hacc hl fit
    have hneg := hnl neg List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e me => hnl e (List.mem_cons_of_mem _ me)
    -- The elements, with a top type past the end of open ones.
    obtain ⟨ty, rest, hty, hrest, run₀, same, fit'⟩ : ∃ ty rest, E ty ∧ (∀ e ∈ rest, E e) ∧
        Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m) (Term.list acc) (.atom tag) (Term.list l)
          (Term.list (neg :: nl)) =
        Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m) (Term.list acc) (.atom tag) (Term.list (ty :: rest))
          (Term.list (neg :: nl)) ∧
        (∀ u, (InT den (tag == "closed") l u ∧ Differs den (neg :: nl) u) ↔
          (InT den (tag == "closed") (ty :: rest) u ∧ Differs den (neg :: nl) u)) ∧
        (tag = "closed" → nl.length ≤ rest.length) := by
      cases l with
      | nil =>
        have op : tag = "open" := by
          rcases g with h | rfl
          · exact h
          · have := fit rfl; simp at this
        subst op
        refine ⟨.atom "term", [], ef.term, by simp, ?_, fun u => ?_, by simp⟩
        · simp only [Term.list]; exact content_nil _ _ _ _ _
        · cases u with
          | nil => simp [Differs]
          | cons y u => simp [InT, ef.den_term y, InT.open_nil]
      | cons ty rest =>
        exact ⟨ty, rest, hl ty List.mem_cons_self, fun e me => hl e (List.mem_cons_of_mem _ me), rfl, fun _ => Iff.rfl,
          fun h => by have := fit h; simp at this; omega⟩
    obtain ⟨df, hdf, rdf, sdf, -⟩ := ef.diff hty hneg
    obtain ⟨mt, hmt, rmt, smt, -⟩ := ef.inter hty hneg
    obtain ⟨ed, red, sed⟩ := empty_bool ef hdf hm
    obtain ⟨em, rem, sem⟩ := empty_bool ef hmt hm
    -- The pieces whose first position outside the negated literal is this one.
    obtain ⟨H, rH, tH, sH⟩ : ∃ H : List Term, (ed = Bool.false ∧ H = [.tuple #[.atom tag, Term.list (acc.reverse ++ df :: rest)]] ∨
        ed = Bool.true ∧ H = []) ∧ (∀ p ∈ H, Piece E p) ∧
        ∀ w, (∃ p ∈ H, PieceIn den p w) ↔ InT den (tag == "closed") (acc.reverse ++ df :: rest) w := by
      cases ed
      · refine ⟨_, Or.inl ⟨rfl, rfl⟩, fun p mp => ?_, fun w => by simp [pieceIn_iff]⟩
        simp at mp; subst mp
        refine ⟨tag, _, rfl, g, fun e me => ?_⟩
        rcases List.mem_append.mp me with me | me
        · exact hacc e (List.mem_reverse.mp me)
        · rcases List.mem_cons.mp me with rfl | me
          · exact hdf
          · exact hrest e me
      · refine ⟨[], Or.inr ⟨rfl, rfl⟩, by simp, fun w => ?_⟩
        simp only [List.not_mem_nil, false_and, exists_false, false_iff]
        intro h
        obtain ⟨v₁, y, v₂, -, -, hy, -⟩ := (InT.mid _ _ _).mp h
        exact sed.mp rfl y hy
    -- The pieces whose first position outside the negated literal is a later one.
    obtain ⟨L, rL, tL, sL⟩ : ∃ L : List Term, (em = Bool.false ∧ Elixir.Module.Types.Descr.«tuple_elim_content/4» (D m)
          (Term.list (mt :: acc)) (.atom tag) (Term.list rest) (Term.list nl) = .ok (Term.list L) ∨ em = Bool.true ∧ L = []) ∧
        (∀ p ∈ L, Piece E p) ∧ ∀ w, (∃ p ∈ L, PieceIn den p w) ↔
          ∃ v₁ y v₂, w = v₁ ++ y :: v₂ ∧ InT den Bool.true acc.reverse v₁ ∧ den mt y ∧ InT den (tag == "closed") rest v₂ ∧
            Differs den nl v₂ := by
      cases em
      · obtain ⟨L, rL, tL, sL⟩ := ih (mt :: acc) rest hnl' (fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact hmt
          · exact hacc e me) hrest fit'
        refine ⟨L, Or.inl ⟨rfl, rL⟩, tL, fun w => ?_⟩
        rw [sL]
        simp only [List.reverse_cons]
        constructor
        · rintro ⟨v₁', u, rfl, h₁, h₂, h₃⟩
          obtain ⟨v₁, y, rfl, h₁, hy⟩ := (inT_last _ _).mp h₁
          exact ⟨v₁, y, u, by simp, h₁, hy, h₂, h₃⟩
        · rintro ⟨v₁, y, v₂, rfl, h₁, hy, h₂, h₃⟩
          exact ⟨v₁ ++ [y], v₂, by simp, (inT_last _ _).mpr ⟨v₁, y, rfl, h₁, hy⟩, h₂, h₃⟩
      · refine ⟨[], Or.inr ⟨rfl, rfl⟩, by simp, fun w => ?_⟩
        simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists, not_and]
        intro _ y _ _ _ hy
        exact absurd hy (sem.mp rfl y)
    refine ⟨H ++ L, ?_, fun p mp => ?_, fun w => ?_⟩
    · rw [run₀, Elixir.Module.Types.Descr.«tuple_elim_content/4».eq_def]
      simp only [Term.list]
      rcases rH with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases rL with ⟨rfl, rL⟩ | ⟨rfl, rfl⟩
      · have rev := reverse_list acc (df :: rest)
        have app := append_list [.tuple #[.atom tag, Term.list (acc.reverse ++ df :: rest)]] L
        simp only [Term.list] at rL rev app
        simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, rev, rL, app]
      · have rev := reverse_list acc (df :: rest)
        have app := append_list [.tuple #[.atom tag, Term.list (acc.reverse ++ df :: rest)]] []
        simp only [Term.list] at rev app
        simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, rev, app]
      · have app := append_list [] L
        simp only [Term.list] at rL app
        simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, rL, app]
      · simp [rdf m hm, rmt m hm, red, rem, Lynx.Term.isMember, boolAtom, Erlang.erlang.«++/2»]
    · rcases List.mem_append.mp mp with mp | mp
      · exact tH p mp
      · exact tL p mp
    · have split : (∃ p ∈ H ++ L, PieceIn den p w) ↔ (∃ p ∈ H, PieceIn den p w) ∨ ∃ p ∈ L, PieceIn den p w := by
        simp only [List.mem_append, or_and_right, exists_or]
      rw [split, sH, sL, InT.mid]
      constructor
      · rintro (⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ | ⟨v₁, y, v₂, rfl, h₁, hy, h₂, h₃⟩)
        · obtain ⟨a, b⟩ := (sdf y).mp hy
          exact ⟨v₁, y :: v₂, rfl, h₁, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inl b⟩).1, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inl b⟩).2⟩
        · obtain ⟨a, b⟩ := (smt y).mp hy
          exact ⟨v₁, y :: v₂, rfl, h₁, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inr h₃⟩).1, ((same (y :: v₂)).mpr ⟨⟨a, h₂⟩, Or.inr h₃⟩).2⟩
      · rintro ⟨v₁, u, rfl, h₁, h₂, h₃⟩
        have := (same u).mp ⟨h₂, h₃⟩
        cases u with
        | nil => exact this.2.elim
        | cons y v₂ =>
          obtain ⟨⟨a, b⟩, c⟩ := this
          by_cases hn : den neg y
          · rcases c with c | c
            · exact absurd hn c
            · exact Or.inr ⟨v₁, y, v₂, rfl, h₁, (smt y).mpr ⟨a, hn⟩, b, c⟩
          · exact Or.inl ⟨v₁, y, v₂, rfl, h₁, (sdf y).mpr ⟨a, hn⟩, b⟩
end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- A closed literal of elements filled with top types up to a size. -/
def closedFill (l : List Term) (j : Nat) : Term :=
  .tuple #[.atom "closed", Term.list (l ++ List.replicate (j - l.length) (.atom "term"))]

theorem elim_sizes_run (l : List Term) (m : Nat) : ∀ (k i : Nat), m - i = k → l.length ≤ i → ∀ acc : List Term,
    Elixir.Module.Types.Descr.«tuple_elim_sizes/4» (.integer i) (.integer m) (Term.list l) (Term.list acc) =
      .ok (Term.list (((List.range' i (m - i)).map (closedFill l)).reverse ++ acc))
  | 0, i, hk, _, acc => by
    have : ¬(i : Int) < m := by omega
    rw [Elixir.Module.Types.Descr.«tuple_elim_sizes/4».eq_def]
    simp [Erlang.erlang.«</2», Int.compare_eq_lt, this, hk]
  | k + 1, i, hk, hl, acc => by
    have lt : (i : Int) < m := by omega
    have ih := elim_sizes_run l m k (i + 1) (by omega) (by omega) (closedFill l i :: acc)
    have range : List.range' i (m - i) = i :: List.range' (i + 1) (m - (i + 1)) := by
      rw [show m - i = (m - (i + 1)) + 1 by omega, List.range'_succ]
    rw [Elixir.Module.Types.Descr.«tuple_elim_sizes/4».eq_def]
    rw [show (((i + 1 : Nat) : Int)) = (i : Int) + 1 by omega] at ih
    simp only [Term.list, closedFill] at ih
    simp [Erlang.erlang.«</2», Int.compare_eq_lt, lt, fill_list l i hl, ih, range,
      closedFill]

theorem pieceIn_closedFill {l : List Term} {j : Nat} (hl : l.length ≤ j) (hterm : ∀ y, den (.atom "term") y)
    (w : List V) : PieceIn den (closedFill l j) w ↔ InT den Bool.false l w ∧ w.length = j := by
  rw [closedFill, pieceIn_iff]
  simp only [show ("closed" == "closed") = Bool.true from rfl]
  constructor
  · intro h
    obtain ⟨a, b⟩ := InT.fill h
    exact ⟨a, by omega⟩
  · rintro ⟨h, rfl⟩
    exact inT_fill_closed h hterm

theorem sizes_sem {l : List Term} {i m : Nat} (hl : l.length ≤ i) (hterm : ∀ y, den (.atom "term") y) (w : List V) :
    (∃ p ∈ ((List.range' i (m - i)).map (closedFill l)).reverse, PieceIn den p w) ↔
      InT den Bool.false l w ∧ i ≤ w.length ∧ w.length < m := by
  simp only [List.mem_reverse, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨p, ⟨j, ⟨k, hk, rfl⟩, rfl⟩, hp⟩
    obtain ⟨a, b⟩ := (pieceIn_closedFill (by omega) hterm w).mp hp
    exact ⟨a, by omega, by omega⟩
  · rintro ⟨a, b, c⟩
    exact ⟨_, ⟨w.length, ⟨w.length - i, by omega, by omega⟩, rfl⟩,
      (pieceIn_closedFill (by omega) hterm w).mpr ⟨a, rfl⟩⟩

theorem sizes_piece (ef : EF nd E V den tl K) {l : List Term} (hl : ∀ e ∈ l, E e) {i m : Nat} :
    ∀ p ∈ ((List.range' i (m - i)).map (closedFill l)).reverse, Piece E p := by
  intro p mp
  simp only [List.mem_reverse, List.mem_map] at mp
  obtain ⟨j, -, rfl⟩ := mp
  refine ⟨"closed", _, rfl, Or.inr rfl, fun e me => ?_⟩
  rcases List.mem_append.mp me with me | me
  · exact hl e me
  · rw [List.eq_of_mem_replicate me]; exact ef.term

/-- `tuple_elim_size/5` gives the tuples of an open literal of sizes outside a negated literal. -/
theorem elim_size_open (ef : EF nd E V den tl K) {ntag : String} (ng : ntag = "open" ∨ ntag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) (m : Nat) (fit : ntag = "closed" → l.length ≤ m + 1) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_elim_size/5» (.integer l.length) (.integer m) (.atom "open") (Term.list l)
        (.atom ntag) = .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den Bool.false l w ∧ (w.length < m ∨ (ntag = "closed" ∧ m + 1 ≤ w.length)) := by
  have sizes := elim_sizes_run l m (m - l.length) l.length rfl (Nat.le_refl _)
  rcases ng with rfl | rfl
  · refine ⟨((List.range' l.length (m - l.length)).map (closedFill l)).reverse ++ [], ?_, ?_, fun w => ?_⟩
    · have := sizes []
      simp [Elixir.Module.Types.Descr.«tuple_elim_size/5», Erlang.erlang.«==/2», Term.list] at this ⊢
      exact this
    · simpa using sizes_piece ef hl
    · rw [List.append_nil, sizes_sem (Nat.le_refl _) ef.den_term w]
      constructor
      · rintro ⟨a, -, c⟩; exact ⟨a, Or.inl c⟩
      · rintro ⟨a, c | ⟨h, -⟩⟩
        · exact ⟨a, a.length_le, c⟩
        · simp at h
  · have hf := fit rfl
    let top : Term := .tuple #[.atom "open", Term.list (l ++ List.replicate (m + 1 - l.length) (.atom "term"))]
    refine ⟨((List.range' l.length (m - l.length)).map (closedFill l)).reverse ++ [top], ?_, ?_, fun w => ?_⟩
    · have := sizes [top]
      have fl : Elixir.Module.Types.Descr.«tuple_fill/2» (Term.list l) (.integer ((m : Int) + 1)) =
          .ok (Term.list (l ++ List.replicate (m + 1 - l.length) (.atom "term"))) := by
        simpa using fill_list l (m + 1) hf
      simp [Elixir.Module.Types.Descr.«tuple_elim_size/5», Erlang.erlang.«==/2», fl] at this ⊢
      exact this
    · intro p mp
      rcases List.mem_append.mp mp with mp | mp
      · exact sizes_piece ef hl p mp
      · simp at mp; subst mp
        refine ⟨"open", _, rfl, Or.inl rfl, fun e me => ?_⟩
        rcases List.mem_append.mp me with me | me
        · exact hl e me
        · rw [List.eq_of_mem_replicate me]; exact ef.term
    · have split : (∃ p ∈ ((List.range' l.length (m - l.length)).map (closedFill l)).reverse ++ [top], PieceIn den p w) ↔
          (∃ p ∈ ((List.range' l.length (m - l.length)).map (closedFill l)).reverse, PieceIn den p w) ∨
            PieceIn den top w := by
        simp only [List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left]
      rw [split, sizes_sem (Nat.le_refl _) ef.den_term w, pieceIn_iff]
      simp only [show ("open" == "closed") = Bool.false from rfl, true_and]
      constructor
      · rintro (⟨a, -, c⟩ | h)
        · exact ⟨a, Or.inl c⟩
        · obtain ⟨a, b⟩ := InT.fill_open h
          exact ⟨a, Or.inr (by omega)⟩
      · rintro ⟨a, c | c⟩
        · exact Or.inl ⟨a, a.length_le, c⟩
        · exact Or.inr (inT_fill_open _ a (by omega) ef.den_term)

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem orElse_bool (a : Bool) (x : Except Exception Term) :
    Lynx.Except.orElse (.ok (boolAtom a)) x = if a then .ok (.atom "true") else x := by
  cases a <;> rfl

theorem tag_closed {tag : String} (g : tag = "open" ∨ tag = "closed") :
    Erlang.erlang.«==/2» (.atom tag) (.atom "closed") = .ok (boolAtom (decide (tag = "closed"))) := by
  rcases g with rfl | rfl <;> simp [Erlang.erlang.«==/2», boolAtom]

/-- `tuple_eliminate_single_negation/3` gives literals holding the tuples of a literal outside a negated literal. -/
theorem elim_single (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag ntag : String} (g : tag = "open" ∨ tag = "closed")
    (ng : ntag = "open" ∨ ntag = "closed") {l nl : List Term} (hl : ∀ e ∈ l, E e) (hnl : ∀ e ∈ nl, E e) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_eliminate_single_negation/3» (D m) (.atom tag) (Term.list l)
        (.tuple #[.atom ntag, Term.list nl]) = .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ ¬InT den (ntag == "closed") nl w := by
  obtain ⟨zb, rz, sz⟩ := zip_empty_run (den := den) ef hm l nl hl hnl
  have c₁ : Lynx.Except.andAlso (Erlang.erlang.«==/2» (.atom tag) (.atom "closed"))
      (Erlang.erlang.«</2» (.integer l.length) (.integer nl.length)) =
        .ok (boolAtom (decide (tag = "closed" ∧ l.length < nl.length))) := by
    rw [tag_closed g]
    by_cases h₁ : tag = "closed" <;> by_cases h₂ : l.length < nl.length <;>
      simp [Lynx.Except.andAlso, boolAtom, h₁, h₂, Erlang.erlang.«</2», Int.compare_eq_lt]
  have c₂ : Lynx.Except.andAlso (Erlang.erlang.«==/2» (.atom ntag) (.atom "closed"))
      (Erlang.erlang.«>/2» (.integer l.length) (.integer nl.length)) =
        .ok (boolAtom (decide (ntag = "closed" ∧ nl.length < l.length))) := by
    rw [tag_closed ng]
    by_cases h₁ : ntag = "closed" <;> by_cases h₂ : nl.length < l.length <;>
      simp [Lynx.Except.andAlso, boolAtom, h₁, h₂, Erlang.erlang.«>/2», Int.compare_eq_gt]
  have closedLen : ∀ {w : List V}, InT den (tag == "closed") l w → tag = "closed" → w.length = l.length := by
    intro w h c; subst c; exact h.closed_length
  by_cases cond : (tag = "closed" ∧ l.length < nl.length) ∨ (ntag = "closed" ∧ nl.length < l.length) ∨ zb = Bool.true
  · refine ⟨[.tuple #[.atom tag, Term.list l]], ?_, fun p mp => ?_, fun w => ?_⟩
    · simp only [Elixir.Module.Types.Descr.«tuple_eliminate_single_negation/3», length_list, Lynx.Except.ok_bind, c₁, c₂,
        orElse_bool, rz]
      rcases cond with h | h | h
      · simp [h, boolAtom, Lynx.Term.isMember, Term.list]
      · by_cases h' : tag = "closed" ∧ l.length < nl.length
        · simp [h', boolAtom, Lynx.Term.isMember, Term.list]
        · simp [h, h', boolAtom, Lynx.Term.isMember, Term.list]
      · by_cases h' : tag = "closed" ∧ l.length < nl.length
        · simp [h', boolAtom, Lynx.Term.isMember, Term.list]
        by_cases h'' : ntag = "closed" ∧ nl.length < l.length
        · simp [h', h'', boolAtom, Lynx.Term.isMember, Term.list]
        · simp [h, h', h'', boolAtom, Lynx.Term.isMember, Term.list]
    · simp at mp; subst mp; exact ⟨tag, l, rfl, g, hl⟩
    · simp only [List.mem_singleton, exists_eq_left, pieceIn_iff]
      refine ⟨fun h => ⟨h, fun hn => ?_⟩, fun h => h.1⟩
      rcases cond with ⟨c, lt⟩ | ⟨c, lt⟩ | z
      · have := closedLen h c; have := hn.length_le; omega
      · subst c; have := hn.closed_length; have := h.length_le; omega
      · exact sz z w (InT.iff_open.mp h).1 (InT.iff_open.mp hn).1
  · simp only [not_or, not_and, Nat.not_lt, Bool.not_eq_true] at cond
    obtain ⟨n₁, n₂, rfl⟩ := cond
    -- The sizes outside the negated literal.
    obtain ⟨S, rS, tS, sS⟩ : ∃ S, Elixir.Module.Types.Descr.«tuple_elim_size/5» (.integer l.length) (.integer nl.length)
        (.atom tag) (Term.list l) (.atom ntag) = .ok (Term.list S) ∧ (∀ p ∈ S, Piece E p) ∧
        ∀ w, (∃ p ∈ S, PieceIn den p w) ↔ tag = "open" ∧ InT den Bool.false l w ∧
          (w.length < nl.length ∨ (ntag = "closed" ∧ nl.length + 1 ≤ w.length)) := by
      rcases g with rfl | rfl
      · obtain ⟨S, rS, tS, sS⟩ := elim_size_open (den := den) ef ng hl nl.length (fun h => by have := n₂ h; omega)
        exact ⟨S, rS, tS, fun w => by rw [sS]; simp⟩
      · exact ⟨[], by simp [Elixir.Module.Types.Descr.«tuple_elim_size/5», Term.list], by simp, by simp⟩
    obtain ⟨C, rC, tC, sC⟩ := elim_content (den := den) ef hm g nl [] l hnl (by simp) hl n₁
    refine ⟨S ++ C, ?_, fun p mp => ?_, fun w => ?_⟩
    · have app := append_list S C
      have d₁ : decide (tag = "closed" ∧ l.length < nl.length) = Bool.false := by
        simp only [decide_eq_false_iff_not, not_and, Nat.not_lt]; exact n₁
      have d₂ : decide (ntag = "closed" ∧ nl.length < l.length) = Bool.false := by
        simp only [decide_eq_false_iff_not, not_and, Nat.not_lt]; exact n₂
      simp only [Elixir.Module.Types.Descr.«tuple_eliminate_single_negation/3», length_list, Lynx.Except.ok_bind, c₁, c₂,
        d₁, d₂, orElse_bool, rz]
      simp [boolAtom, Lynx.Term.isMember, rS, rC, app]
    · rcases List.mem_append.mp mp with mp | mp
      · exact tS p mp
      · exact tC p mp
    · have split : (∃ p ∈ S ++ C, PieceIn den p w) ↔ (∃ p ∈ S, PieceIn den p w) ∨ ∃ p ∈ C, PieceIn den p w := by
        simp only [List.mem_append, or_and_right, exists_or]
      have content : (∃ p ∈ C, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ Differs den nl w := by
        rw [sC]
        constructor
        · rintro ⟨v₁, u, rfl, h₁, h₂, h₃⟩
          have : v₁ = [] := by cases v₁ <;> simp_all [InT]
          subst this; exact ⟨h₂, h₃⟩
        · rintro ⟨h₂, h₃⟩; exact ⟨[], w, rfl, trivial, h₂, h₃⟩
      rw [split, sS, content, inT_iff_differs nl w]
      constructor
      · rintro (⟨rfl, h, c⟩ | ⟨h, d⟩)
        · refine ⟨h, fun ⟨a, _, b⟩ => ?_⟩
          rcases c with c | ⟨rfl, c⟩
          · omega
          · have := b rfl; omega
        · exact ⟨h, fun hh => hh.2.1 d⟩
      · rintro ⟨h, hn⟩
        by_cases d : Differs den nl w
        · exact Or.inr ⟨h, d⟩
        · left
          have hn' : ¬(nl.length ≤ w.length ∧ ((ntag == "closed") = Bool.true → w.length = nl.length)) :=
            fun ⟨a, b⟩ => hn ⟨a, d, b⟩
          rcases g with rfl | rfl
          · refine ⟨rfl, h, ?_⟩
            by_cases lt : w.length < nl.length
            · exact Or.inl lt
            · rcases ng with rfl | rfl
              · exact absurd ⟨by omega, fun h => by simp at h⟩ hn'
              · exact Or.inr ⟨rfl, by
                  by_cases e : w.length = nl.length
                  · exact absurd ⟨by omega, fun _ => e⟩ hn'
                  · omega⟩
          · exfalso
            have len := closedLen h rfl
            have := n₁ rfl
            rcases ng with rfl | rfl
            · exact hn' ⟨by omega, fun h => by simp at h⟩
            · have := n₂ rfl; exact hn' ⟨by omega, fun _ => by omega⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `tuple_eliminate_negations/3` gives literals holding the tuples of a line. -/
theorem elim_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {tag : String} (g : tag = "open" ∨ tag = "closed")
    {l : List Term} (hl : ∀ e ∈ l, E e) (negs : List Term) (lits : ∀ N ∈ negs, TupleLit E N) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_eliminate_negations/3» (D (n + 2)) (.atom tag) (Term.list l) (Term.list negs) =
        .ok (Term.list P) ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ ∀ N ∈ negs, ¬LitSem den N w := by
  obtain ⟨r, ⟨P, rfl, tP, sP⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr"
    "-tuple_eliminate_negations/3-fun-1-" #[]
    (fun pre a => ∃ P, a = Term.list P ∧ (∀ p ∈ P, Piece E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ InT den (tag == "closed") l w ∧ ∀ N ∈ pre, ¬LitSem den N w) negs
    (fun pre x a mx ⟨A, ea, tA, sA⟩ => by
      subst ea
      obtain ⟨k, ntag, nl, rfl, ng, hnl⟩ := lits x mx
      have each : ∀ p ∈ A, ∃ Q, Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-0-/3» (D n) (Term.list nl)
          (.atom ntag) p = .ok (Term.list Q) ∧ (∀ q ∈ Q, Piece E q) ∧
          ∀ w, (∃ q ∈ Q, PieceIn den q w) ↔ PieceIn den p w ∧ ¬InT den (ntag == "closed") nl w := by
        intro p mp
        obtain ⟨tag', l', rfl, g', hl'⟩ := tA p mp
        obtain ⟨Q, rQ, tQ, sQ⟩ := elim_single (den := den) ef hn g' ng hl' hnl
        refine ⟨Q, ?_, tQ, fun w => by rw [sQ, pieceIn_iff]⟩
        simpa [Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-0-/3»] using rQ
      classical
      let h : Term → List Term := fun p => if hp : p ∈ A then Classical.choose (each p hp) else []
      have hh : ∀ p ∈ A, Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-0-/3» (D n) (Term.list nl)
          (.atom ntag) p = .ok (Term.list (h p)) ∧ (∀ q ∈ h p, Piece E q) ∧
          ∀ w, (∃ q ∈ h p, PieceIn den q w) ↔ PieceIn den p w ∧ ¬InT den (ntag == "closed") nl w := by
        intro p mp
        simp only [h, dite_eq_left mp]
        exact Classical.choose_spec (each p mp)
      have fm := flatmap_lists (m := n + 1) "Elixir.Module.Types.Descr" "-tuple_eliminate_negations/3-fun-0-"
        #[Term.list nl, .atom ntag] h A (fun p mp => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_eliminate_negations/3-fun-0-/1».pure]
          exact (hh p mp).1)
      refine ⟨Term.list (A.flatMap h), ⟨A.flatMap h, rfl, fun q mq => ?_, fun w => ?_⟩, ?_⟩
      · obtain ⟨p, mp, mq⟩ := List.mem_flatMap.mp mq
        exact (hh p mp).2.1 q mq
      · have lit : LitSem den (.tuple #[.integer k, .atom ntag, Term.list nl]) w ↔ InT den (ntag == "closed") nl w :=
          ⟨lit_sem, fun h => ⟨k, ntag, nl, rfl, h⟩⟩
        constructor
        · rintro ⟨q, mq, hq⟩
          obtain ⟨p, mp, mq⟩ := List.mem_flatMap.mp mq
          obtain ⟨hp, hn⟩ := ((hh p mp).2.2 w).mp ⟨q, mq, hq⟩
          obtain ⟨a, b⟩ := (sA w).mp ⟨p, mp, hp⟩
          refine ⟨a, fun N mN => ?_⟩
          rcases List.mem_append.mp mN with mN | mN
          · exact b N mN
          · simp at mN; subst mN; rw [lit]; exact hn
        · rintro ⟨a, b⟩
          obtain ⟨p, mp, hp⟩ := (sA w).mpr ⟨a, fun N mN => b N (List.mem_append_left _ mN)⟩
          obtain ⟨q, mq, hq⟩ := ((hh p mp).2.2 w).mpr ⟨hp, fun hn => b _ (by simp) (lit.mpr hn)⟩
          exact ⟨q, List.mem_flatMap.mpr ⟨p, mp, mq⟩, hq⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_eliminate_negations/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_eliminate_negations/3-fun-1-/2»] using fm)
    (Term.list [.tuple #[.atom tag, Term.list l]])
    ⟨[.tuple #[.atom tag, Term.list l]], rfl, fun p mp => by simp at mp; subst mp; exact ⟨tag, l, rfl, g, hl⟩,
      fun w => by simp [pieceIn_iff]⟩
  exact ⟨P, by simpa [Elixir.Module.Types.Descr.«tuple_eliminate_negations/3»] using run, tP, sP⟩

/-- `tuple_bdd_to_dnf_no_negations/1` gives literals holding the tuples of a BDD. -/
theorem no_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {r : Term} (wr : Bdd (TLit E) r) :
    ∃ P, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (n + 3)) r = .ok (Term.list P) ∧
      (∀ p ∈ P, Piece E p) ∧ ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ eval (valT E den w) r = Bool.true := by
  obtain ⟨all, run, tl', sl⟩ := dnf_tuple (den := den) ef.opsU ef.msemZ (m := n + 3) (by omega) wr (fun t h => h.1) []
    (.tuple #[.atom "open", .nil]) [] ⟨"open", [], rfl, Or.inl rfl, by simp⟩ (by simp)
  have each : ∀ L ∈ all, ∃ Q, Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1» (D (n + 2)) L =
      .ok (Term.list Q) ∧ (∀ q ∈ Q, Piece E q) ∧ ∀ w, (∃ q ∈ Q, PieceIn den q w) ↔ InLine den L w := by
    intro L mL
    obtain ⟨tag, l, negs, rfl, g, hl, lits⟩ := tl' L mL
    obtain ⟨b, check, -, empty⟩ := elements_exact ef.opsU ef.msemZ rfl l hl
    cases b
    · obtain ⟨Q, rQ, tQ, sQ⟩ := elim_negs (den := den) ef hn g hl negs lits
      refine ⟨Q, ?_, tQ, fun w => by rw [sQ, inLine_iff]⟩
      simp [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1», check (n + 2) (by omega), boolAtom,
        Lynx.Term.isMember, rQ]
    · refine ⟨[], ?_, by simp, fun w => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1», check (n + 2) (by omega), boolAtom,
          Lynx.Term.isMember, Term.list]
      · simp only [List.not_mem_nil, false_and, exists_false, false_iff]
        intro hv
        obtain ⟨hv, -⟩ := inLine_iff.mp hv
        obtain ⟨e, me, he⟩ := empty rfl
        obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem me
        obtain ⟨v₁, y, v₂, -, -, hy, -⟩ := (InT.mid l₁ e l₂).mp hv
        exact he y hy
  classical
  let h : Term → List Term := fun L => if hL : L ∈ all then Classical.choose (each L hL) else []
  have hh : ∀ L ∈ all, Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_no_negations/1-fun-0-/1» (D (n + 2)) L =
      .ok (Term.list (h L)) ∧ (∀ q ∈ h L, Piece E q) ∧ ∀ w, (∃ q ∈ h L, PieceIn den q w) ↔ InLine den L w := by
    intro L mL
    simp only [h, dite_eq_left mL]
    exact Classical.choose_spec (each L mL)
  have fm := flatmap_lists (m := n + 3) "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_no_negations/1-fun-0-" #[] h all
    (fun L mL => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_no_negations/1-fun-0-/1».pure]
      exact (hh L mL).1)
  obtain ⟨P, rd, sub, cover⟩ := dedup_run _ (all.flatMap h) (Nat.le_refl _)
  have pieces : ∀ q ∈ all.flatMap h, Piece E q := fun q mq => by
    obtain ⟨L, mL, mq⟩ := List.mem_flatMap.mp mq
    exact (hh L mL).2.1 q mq
  refine ⟨P, ?_, fun p mp => pieces p (sub p mp), fun w => ?_⟩
  · have run' : Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D (n + 3)) .nil (.tuple #[.atom "open", .nil]) .nil r =
        .ok (Term.list all) := by simpa using run
    simp [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1», run', fm, rd]
  · have hp : InPos den (.tuple #[.atom "open", .nil]) w := ⟨"open", [], rfl, InT.open_nil w⟩
    rw [← (by simpa [hp] using sl w : (∃ L ∈ all, InLine den L w) ↔ eval (valT E den w) r = Bool.true)]
    constructor
    · rintro ⟨p, mp, hp⟩
      obtain ⟨L, mL, mq⟩ := List.mem_flatMap.mp (sub p mp)
      exact ⟨L, mL, ((hh L mL).2.2 w).mp ⟨p, mq, hp⟩⟩
    · rintro ⟨L, mL, hL⟩
      obtain ⟨q, mq, hq⟩ := ((hh L mL).2.2 w).mpr hL
      have mq' : q ∈ all.flatMap h := List.mem_flatMap.mpr ⟨L, mL, mq⟩
      obtain ⟨p, mp, c⟩ := cover q mq'
      exact ⟨p, mp, pieceIn_congr ef.msemZ (pieces p (sub p mp)) (pieces q mq') (Lynx.Term.compare_eq_symm c) hq⟩

end

end Elixir.STTDescrProofsTest.Nest
