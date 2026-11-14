namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-- The general clause of `tuple_line_empty?/4`. -/
theorem line_cons (d : Dispatcher) (tag : String) (l : List Term) (k : Int) (ntag : String) (nl rest : List Term)
    (S : Term) (notTop : ¬(ntag = "open" ∧ nl = [])) (notLast : ¬(tag = "open" ∧ ntag = "closed" ∧ rest = [])) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom tag) (Term.list l)
        (.cons (.tuple #[.integer k, .atom ntag, Term.list nl]) (Term.list rest)) S =
      if (tag = "closed" ∧ l.length < nl.length) ∨ (ntag = "closed" ∧ nl.length < l.length) then
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom tag) (Term.list l) (Term.list rest) S
      else Lynx.Except.andAlso
        (Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d .nil (.atom tag) (Term.list l) (Term.list nl)
          (Term.list rest) S)
        (Elixir.Module.Types.Descr.«tuple_empty_arity?/7» d (.integer l.length) (.integer nl.length) (.atom tag)
          (Term.list l) (.atom ntag) (Term.list rest) S) true := by
  rw [Elixir.Module.Types.Descr.«tuple_line_empty?/4».eq_def]
  have listNil : ∀ xs : List Term, Term.list xs = .nil ↔ xs = [] := by
    intro xs; cases xs <;> simp [Term.list]
  split
  · rename_i heq; simp at heq
  · rename_i heq
    simp [listNil] at heq
    exact absurd ⟨heq.1.2.1, heq.1.2.2⟩ notTop
  · rename_i htag heq
    simp [listNil] at heq htag
    exact absurd ⟨htag, heq.1.2.1, heq.2⟩ notLast
  · rename_i heq _
    simp at heq
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
    simp [length_list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Lynx.Except.orElse,
      Lynx.Except.andAlso]
    by_cases tc : tag = "closed" <;> by_cases nc : ntag = "closed" <;>
      rcases Nat.lt_trichotomy l.length nl.length with h | h | h <;>
      simp [tc, nc, h, Int.compare_eq_lt, Int.compare_eq_gt, Nat.lt_irrefl, Nat.lt_asymm] <;>
      omega
  · rename_i h₄ _
    exact (h₄ _ _ _ _ rfl).elim

theorem reverse_list (l t : List Term) :
    Erlang.lists.«reverse/2» (Term.list l) (Term.list t) = .ok (Term.list (l.reverse ++ t)) := by
  induction l generalizing t with
  | nil => simp [Erlang.lists.«reverse/2»]
  | cons h rest ih =>
    have := ih (h :: t)
    simp [Term.list, Erlang.lists.«reverse/2»] at this ⊢
    exact this

theorem reverse_tail (l : List Term) (t : Term) :
    Erlang.lists.«reverse/2» (Term.list l) t = .ok (l.foldl (fun a x => .cons x a) t) := by
  induction l generalizing t with
  | nil => simp [Erlang.lists.«reverse/2»]
  | cons h rest ih =>
    have := ih (.cons h t)
    simp [Erlang.lists.«reverse/2»] at this ⊢
    exact this

theorem list_reverse_append (l t : List Term) :
    Term.list (l.reverse ++ t) = l.foldl (fun a x => .cons x a) (Term.list t) := by
  induction l generalizing t with
  | nil => simp
  | cons h rest ih => simp [ih (h :: t), Term.list]

theorem elements_done (d : Dispatcher) (acc tag l rest S : Term) :
    Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d acc tag l .nil rest S = .ok (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def]
  rfl

/-- One step of `tuple_elements_empty?/6`, which checks the element `ty` against the negated element `nt`. -/
theorem elements_step (d : Dispatcher) (acc : List Term) (tag : Term) (l : List Term) (nt : Term)
    (nl : List Term) (rest S ty : Term) (es : List Term)
    (hl : (l = [] ∧ ty = .atom "term" ∧ es = []) ∨ l = ty :: es) (meet : Term)
    (hmeet : Elixir.Module.Types.Descr.«bare_intersection/2» d ty nt = .ok meet) :
    (Elixir.Module.Types.Descr.«empty_seen?/2» d meet S = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list acc) tag (Term.list l) (.cons nt (Term.list nl))
        rest S = Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag (Term.list (acc.reverse ++ ty :: es)) rest S) ∧
    (∀ diff, Elixir.Module.Types.Descr.«empty_seen?/2» d meet S = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«bare_difference/2» d ty nt = .ok diff →
      (Elixir.Module.Types.Descr.«empty_seen?/2» d diff S = .ok (.atom "true") →
        Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list acc) tag (Term.list l)
          (.cons nt (Term.list nl)) rest S =
        Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list (ty :: acc)) tag (Term.list es)
          (Term.list nl) rest S) ∧
      (Elixir.Module.Types.Descr.«empty_seen?/2» d diff S = .ok (.atom "false") →
        Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list acc) tag (Term.list l)
          (.cons nt (Term.list nl)) rest S =
        Lynx.Except.andAlso
          (Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag (Term.list (acc.reverse ++ diff :: es)) rest S)
          (Elixir.Module.Types.Descr.«tuple_elements_empty?/6» d (Term.list (meet :: acc)) tag (Term.list es)
            (Term.list nl) rest S) true)) := by
  refine ⟨fun empty => ?_, fun diff full hdiff => ⟨fun emptyD => ?_, fun fullD => ?_⟩⟩ <;>
    rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/6».eq_def] <;>
    rcases hl with ⟨rfl, rfl, rfl⟩ | rfl
  all_goals simp [Term.list, isMember, reverse_tail, list_reverse_append, *]

theorem dup_list (x : Term) : ∀ (n : Nat) (t : List Term),
    Erlang.lists.«duplicate/3» (Term.integer n) x (Term.list t) = .ok (Term.list (List.replicate n x ++ t)) := by
  intro n
  induction n with
  | zero => intro t; rw [Erlang.lists.«duplicate/3».eq_def]; simp
  | succ n ih =>
    intro t
    rw [Erlang.lists.«duplicate/3».eq_def]
    have := ih (x :: t)
    simp only [Term.list] at this
    split
    · rename_i h; simp at h; omega
    · simp [this, List.replicate_succ', List.append_assoc]

theorem dup_nat (x : Term) (n : Nat) :
    Erlang.lists.«duplicate/2» (.integer n) x = .ok (Term.list (List.replicate n x)) := by
  have := dup_list x n []
  simp only [List.append_nil, Term.list] at this
  simp [Erlang.lists.«duplicate/2», Erlang.erlang.«>=/2», Erlang.erlang.«and/2», this,
    Int.isGE_compare]

theorem append_list (a b : List Term) : Erlang.erlang.«++/2» (Term.list a) (Term.list b) = .ok (Term.list (a ++ b)) := by
  induction a with
  | nil => simp [Erlang.erlang.«++/2»]
  | cons h t ih => simp [Term.list, Erlang.erlang.«++/2»] at ih ⊢; simp [ih]

theorem fill_list (l : List Term) (k : Nat) (h : l.length ≤ k) :
    Elixir.Module.Types.Descr.«tuple_fill/2» (Term.list l) (.integer k) =
      .ok (Term.list (l ++ List.replicate (k - l.length) (Term.atom "term"))) := by
  have pad : ((k : Int) - (l.length : Int)) = ((k - l.length : Nat) : Int) := by omega
  have nonneg : ¬((k - l.length : Nat) : Int) < 0 := by omega
  simp [Elixir.Module.Types.Descr.«tuple_fill/2», length_list, pad, nonneg, dup_nat, append_list]

/-- `tuple_empty_sizes?/5` checks the closed tuples of each size from `i` below `m`. -/
theorem sizes_all (d : Dispatcher) (l : List Term) (m : Nat) (rest S : Term)
    (lines : ∀ i, l.length ≤ i → i < m → Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed")
      (Term.list (l ++ List.replicate (i - l.length) (Term.atom "term"))) rest S = .ok (Term.atom "true")) :
    ∀ i, l.length ≤ i → Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer i) (.integer m)
      (Term.list l) rest S = .ok (.atom "true") := by
  intro i le
  induction h : m - i generalizing i with
  | zero =>
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have : ¬(i : Int) < m := by omega
    simp [this]
  | succ k ih =>
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have lt : (i : Int) < m := by omega
    have next := ih (i + 1) (by omega) (by omega)
    simp only [Int.natCast_add, Int.natCast_one] at next
    simp [lt, fill_list l i le, lines i le (by omega), Lynx.Except.andAlso, next]

/-- `tuple_empty_arity?/7` holds for closed lines, or when the sizes and the larger open tuples are empty. -/
theorem arity_true (d : Dispatcher) (n m : Nat) (tag : String) (l : List Term) (ntag : String) (rest S : Term)
    (ok : tag = "closed" ∨ (Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer n) (.integer m)
      (Term.list l) rest S = .ok (.atom "true") ∧ (ntag = "open" ∨ (l.length ≤ m + 1 ∧
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open")
          (Term.list (l ++ List.replicate (m + 1 - l.length) (Term.atom "term"))) rest S = .ok (Term.atom "true"))))) :
    Elixir.Module.Types.Descr.«tuple_empty_arity?/7» d (.integer n) (.integer m) (.atom tag) (Term.list l)
      (.atom ntag) rest S = .ok (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
  rcases ok with rfl | ⟨sizes, rfl | ⟨le, line⟩⟩
  · simp [Erlang.erlang.«==/2», Lynx.Except.orElse]
  · by_cases c : tag = "closed"
    · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c]
    · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, sizes, Lynx.Except.andAlso]
  · by_cases c : tag = "closed"
    · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c]
    · have fill := fill_list l (m + 1) le
      simp only [Int.natCast_add, Int.natCast_one] at fill
      by_cases o : ntag = "open"
      · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, sizes, Lynx.Except.andAlso, o]
      · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, sizes, Lynx.Except.andAlso, o, fill, line]

/-- A negated top literal empties any line. -/
theorem line_top (d : Dispatcher) (tag l : Term) (k : Int) (rest S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag l
      (.cons (.tuple #[.integer k, .atom "open", .nil]) rest) S = .ok (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«tuple_line_empty?/4».eq_def]
  split <;> simp_all

/-! Tuple lines whose negations hold `{}` or `{term, ...}`. -/

/-- The empty tuple literal `{}`. -/
def IsE (t : Term) : Prop := ∃ k : Int, t = .tuple #[.integer k, .atom "closed", .nil]

/-- The literal `{term, ...}` of tuples with at least one element. -/
def IsH (t : Term) : Prop := ∃ k : Int, t = .tuple #[.integer k, .atom "open", Term.list [.atom "term"]]

/-- Elements of lines that are not empty, at every call depth from `K`. -/
def Full (E : Term → Prop) (K : Nat) (S : List (Term × Term)) (e : Term) : Prop :=
  E e ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) e (.map S) = .ok (.atom "false")

theorem full_term (ops : ElemOk E K) (S : List (Term × Term)) : Full E K S (.atom "term") :=
  ⟨ops.term, fun m _ => by rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl⟩

theorem andAlso_true : Lynx.Except.andAlso (.ok (.atom "true")) (.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
  simp [Lynx.Except.andAlso]

theorem list_cons (x : Term) (xs : List Term) : Term.list (x :: xs) = .cons x (Term.list xs) := rfl

/-- `{}` minus the negations, which hold `{}`, is empty. -/
theorem line_closed_empty (d : Dispatcher) (S : Term) : ∀ negs : List Term, (∀ t ∈ negs, TupleLit E t) →
    (∃ t ∈ negs, IsE t) →
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed") (Term.list []) (Term.list negs) S =
      .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil => intro _ ⟨t, m, _⟩; simp at m
  | cons N rest ih =>
    intro lits ⟨t, mt, et⟩
    obtain ⟨k, tag', nl, rfl, -, -⟩ := lits N List.mem_cons_self
    rw [list_cons]
    by_cases top : tag' = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact line_top d _ _ k _ S
    rw [line_cons d "closed" [] k tag' nl rest S top (by simp)]
    by_cases m0 : nl = []
    · subst m0
      simp only [List.length_nil, Nat.lt_irrefl, and_false, or_self, ite_false]
      rw [elements_done, arity_true d 0 0 "closed" [] tag' (Term.list rest) S (Or.inl rfl)]
      exact andAlso_true
    · have pos : 0 < nl.length := List.length_pos_iff.mpr m0
      simp only [List.length_nil, pos, and_true, true_or, ite_true]
      refine ih (fun t m => lits t (List.mem_cons_of_mem _ m)) ⟨t, ?_, et⟩
      rcases List.mem_cons.mp mt with rfl | m
      · obtain ⟨k', e⟩ := et
        simp at e
        exact absurd (by cases nl <;> simp_all [Term.list]) m0
      · exact m

/-- Checking each element of a line against a negated literal produces lines of full elements. -/
theorem elements_all (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K ≤ m) (S : List (Term × Term)) (tag rest : Term)
    (lineOk : ∀ l, l ≠ [] → (∀ e ∈ l, Full E K S e) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) tag (Term.list l) rest (.map S) = .ok (.atom "true")) :
    ∀ nl : List Term, (∀ e ∈ nl, E e) → ∀ acc l : List Term, (∀ e ∈ acc, Full E K S e) →
      (∀ e ∈ l, Full E K S e) →
      Elixir.Module.Types.Descr.«tuple_elements_empty?/6» (D m) (Term.list acc) tag (Term.list l)
        (Term.list nl) rest (.map S) = .ok (.atom "true") := by
  intro nl
  induction nl with
  | nil => intro _ acc l _ _; exact elements_done _ _ _ _ _ _
  | cons nt nl ih =>
    intro hnl acc l hacc hl
    obtain ⟨ty, es, hshape, hty, hes⟩ : ∃ ty es, ((l = [] ∧ ty = .atom "term" ∧ es = []) ∨ l = ty :: es) ∧
        Full E K S ty ∧ ∀ e ∈ es, Full E K S e := by
      cases l with
      | nil => exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, full_term ops S, by simp⟩
      | cons x xs => exact ⟨x, xs, Or.inr rfl, hl x List.mem_cons_self, fun e m => hl e (List.mem_cons_of_mem _ m)⟩
    have hnt := hnl nt List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e m => hnl e (List.mem_cons_of_mem _ m)
    obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty.1 hnt
    have step := elements_step (D m) acc tag l nt nl rest (.map S) ty es hshape meet (hmeet m hm)
    rw [list_cons]
    have allRev : ∀ x, Full E K S x → ∀ e ∈ acc.reverse ++ x :: es, Full E K S e := by
      intro x hx e m
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
      rcases m with m | rfl | m
      · exact hacc e m
      · exact hx
      · exact hes e m
    obtain ⟨bm, em⟩ := ops.empty lmeet S
    cases bm
    · have fullMeet : Full E K S meet := ⟨lmeet, fun m' h' => by simpa [boolAtom] using em m' h'⟩
      obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty.1 hnt
      obtain ⟨bd, ed⟩ := ops.empty ldiff S
      cases bd
      · have fullDiff : Full E K S diff := ⟨ldiff, fun m' h' => by simpa [boolAtom] using ed m' h'⟩
        rw [(step.2 _ (fullMeet.2 m hm) (hdiff m hm)).2 (fullDiff.2 m hm),
          lineOk _ (by simp) (allRev diff fullDiff),
          ih hnl' (meet :: acc) es (fun e m => by
            rcases List.mem_cons.mp m with rfl | m
            · exact fullMeet
            · exact hacc e m) hes]
        exact andAlso_true
      · rw [(step.2 _ (fullMeet.2 m hm) (hdiff m hm)).1 (by simpa [boolAtom] using ed m hm)]
        exact ih hnl' (ty :: acc) es (fun e m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact hty
          · exact hacc e m) hes
    · rw [step.1 (by simpa [boolAtom] using em m hm)]
      exact lineOk _ (by simp) (allRev ty hty)

theorem full_fill (ops : ElemOk E K) (S : List (Term × Term)) {l : List Term} (hl : ∀ e ∈ l, Full E K S e)
    (k : Nat) : ∀ e ∈ l ++ List.replicate k (Term.atom "term"), Full E K S e := by
  intro e m
  rcases List.mem_append.mp m with m | m
  · exact hl e m
  · rw [List.eq_of_mem_replicate m]; exact full_term ops S

/-- A line of at least one element minus negations that hold `{term, ...}` is empty. -/
theorem line_full (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K ≤ m) (S : List (Term × Term)) : ∀ negs : List Term,
    (∀ t ∈ negs, TupleLit E t) →
    (∃ t ∈ negs, IsH t) → ∀ (tag : String) (l : List Term), l ≠ [] → (∀ e ∈ l, Full E K S e) →
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom tag) (Term.list l) (Term.list negs) (.map S) =
      .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil => intro _ ⟨t, m, _⟩; simp at m
  | cons N rest ih =>
    intro lits ⟨t, mt, ht⟩ tag l ne hl
    obtain ⟨k, tag', nl, rfl, -, hnl⟩ := lits N List.mem_cons_self
    have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    rw [list_cons]
    by_cases top : tag' = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact line_top _ _ _ k _ (.map S)
    have pos : 0 < l.length := List.length_pos_iff.mpr ne
    by_cases isH : IsH (.tuple #[.integer k, .atom tag', Term.list nl])
    · obtain ⟨k', e⟩ := isH
      simp at e
      obtain ⟨_, htag, hlist⟩ := e
      have hnl : nl = [.atom "term"] := by
        cases nl with
        | nil => simp [Term.list] at hlist
        | cons x xs => cases xs <;> simp_all [Term.list]
      subst htag hnl
      rw [line_cons _ tag l k "open" [.atom "term"] rest (.map S) top (by simp)]
      have cond : ¬((tag = "closed" ∧ l.length < [Term.atom "term"].length) ∨
          ("open" = "closed" ∧ [Term.atom "term"].length < l.length)) := by
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · simp only [List.length_singleton] at h; omega
        · simp at h
      rw [ite_eq_right_of_eq_false _ _ (eq_false cond)]
      obtain ⟨ty, es, rfl⟩ : ∃ ty es, l = ty :: es := by cases l <;> simp_all
      have hty := hl ty List.mem_cons_self
      have step := elements_step (D m) [] (.atom tag) (ty :: es) (.atom "term") [] (Term.list rest) (.map S) ty es
        (Or.inr rfl) ty (inter_term_right _ _)
      have step' := (step.2 _ (hty.2 m hm) (diff_term_right _ _)).1 (empty_none_seen _ _)
      have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D m) (.integer (ty :: es).length)
          (.integer [Term.atom "term"].length) (.atom tag) (Term.list (ty :: es)) (.atom "open") (Term.list rest) (.map S) =
          .ok (.atom "true") := by
        refine arity_true _ _ _ tag _ "open" _ (.map S) ?_
        by_cases c : tag = "closed"
        · exact Or.inl c
        · exact Or.inr ⟨sizes_all _ _ _ _ _ (fun i le lt => by simp at lt le; omega) _ (Nat.le_refl _), Or.inl rfl⟩
      simp only [Term.list] at step' arity ⊢
      rw [step', elements_done, arity]
      exact andAlso_true
    · have hrest : ∃ t ∈ rest, IsH t := by
        rcases List.mem_cons.mp mt with rfl | m
        · exact absurd ht isH
        · exact ⟨t, m, ht⟩
      have notLast : ¬(tag = "open" ∧ tag' = "closed" ∧ rest = []) := by
        rintro ⟨-, -, rfl⟩
        simp at hrest
      rw [line_cons _ tag l k tag' nl rest (.map S) top notLast]
      by_cases cond : (tag = "closed" ∧ l.length < nl.length) ∨ (tag' = "closed" ∧ nl.length < l.length)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true cond)]
        exact ih lits' hrest tag l ne hl
      rw [ite_eq_right_of_eq_false _ _ (eq_false cond),
        elements_all ops dops hm S (.atom tag) (Term.list rest) (fun l' ne' hl' => ih lits' hrest tag l' ne' hl') nl hnl [] l
          (by simp) hl,
        arity_true _ _ _ tag _ tag' _ (.map S) ?_]
      · exact andAlso_true
      by_cases c : tag = "closed"
      · exact Or.inl c
      refine Or.inr ⟨sizes_all _ _ _ _ _ (fun i _ _ => ih lits' hrest "closed" _ (by simp [ne]) (full_fill ops S hl _)) _
        (Nat.le_refl _), ?_⟩
      by_cases o : tag' = "open"
      · exact Or.inl o
      · have closed : tag' = "closed" := by
          rcases lits (.tuple #[.integer k, .atom tag', Term.list nl]) List.mem_cons_self with ⟨_, _, _, e, g, -⟩
          simp at e; obtain ⟨-, rfl, -⟩ := e; rcases g with g | g <;> simp_all
        refine Or.inr ⟨by simp [closed] at cond; omega, ih lits' hrest "open" _ (by simp [ne]) (full_fill ops S hl _)⟩

/-- Any line minus negations that hold both `{}` and `{term, ...}` is empty. -/
theorem line_both (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K ≤ m) (S : List (Term × Term)) (negs : List Term)
    (lits : ∀ t ∈ negs, TupleLit E t)
    (hE : ∃ t ∈ negs, IsE t) (hH : ∃ t ∈ negs, IsH t) (tag : String) (htag : tag = "open" ∨ tag = "closed")
    (l : List Term) (hl : ∀ e ∈ l, Full E K S e) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom tag) (Term.list l) (Term.list negs) (.map S) =
      .ok (.atom "true") := by
  by_cases ne : l ≠ []
  · exact line_full ops dops hm S negs lits hH tag l ne hl
  simp only [ne_eq, Decidable.not_not] at ne
  subst ne
  rcases htag with rfl | rfl
  case inr => exact line_closed_empty _ (.map S) negs lits hE
  obtain ⟨N, rest, rfl⟩ : ∃ N rest, negs = N :: rest := by
    cases negs with
    | nil => obtain ⟨t, m, _⟩ := hE; simp at m
    | cons N rest => exact ⟨N, rest, rfl⟩
  obtain ⟨k, tag', nl, rfl, htag', hnl⟩ := lits _ List.mem_cons_self
  have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
  rw [list_cons]
  by_cases top : tag' = "open" ∧ nl = []
  · obtain ⟨rfl, rfl⟩ := top
    exact line_top _ _ _ k _ (.map S)
  have notE : IsE (.tuple #[.integer k, .atom tag', Term.list nl]) → tag' = "closed" ∧ nl = [] := by
    rintro ⟨k', e⟩
    simp at e
    obtain ⟨-, rfl, e⟩ := e
    exact ⟨rfl, by cases nl <;> simp_all [Term.list]⟩
  have notH : IsH (.tuple #[.integer k, .atom tag', Term.list nl]) → tag' = "open" ∧ nl = [.atom "term"] := by
    rintro ⟨k', e⟩
    simp at e
    obtain ⟨-, rfl, e⟩ := e
    refine ⟨rfl, ?_⟩
    cases nl with
    | nil => simp [Term.list] at e
    | cons x xs => cases xs <;> simp_all [Term.list]
  have inRest : ∀ {P : Term → Prop}, (∃ t ∈ (.tuple #[.integer k, .atom tag', Term.list nl]) :: rest, P t) →
      ¬P (.tuple #[.integer k, .atom tag', Term.list nl]) → ∃ t ∈ rest, P t := by
    intro P ⟨t, m, ht⟩ np
    rcases List.mem_cons.mp m with rfl | m
    · exact absurd ht np
    · exact ⟨t, m, ht⟩
  have notLast : ¬("open" = "open" ∧ tag' = "closed" ∧ rest = []) := by
    rintro ⟨-, rfl, rfl⟩
    obtain ⟨t, m, ht⟩ := hH
    simp at m; subst m
    have := (notH ht).1; simp at this
  rw [line_cons _ "open" [] k tag' nl rest (.map S) top notLast,
    ite_eq_right_of_eq_false _ _ (eq_false (by simp))]
  have closedLines : (∃ t ∈ rest, IsE t) → (∃ t ∈ rest, IsH t) → ∀ i, ([] : List Term).length ≤ i → i < nl.length →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom "closed")
        (Term.list (([] : List Term) ++ List.replicate (i - ([] : List Term).length) (Term.atom "term"))) (Term.list rest) (Term.map S) =
          .ok (.atom "true") := by
    intro hE' hH' i _ _
    cases i with
    | zero => exact line_closed_empty _ (.map S) rest lits' hE'
    | succ i => exact line_full ops dops hm S rest lits' hH' "closed" _ (by simp) (full_fill ops S (by simp) _)
  by_cases isH : IsH (.tuple #[.integer k, .atom tag', Term.list nl])
  · obtain ⟨rfl, rfl⟩ := notH isH
    have hE' := inRest hE fun e => by have := (notE e).1; simp at this
    have step := elements_step (D m) [] (.atom "open") [] (.atom "term") [] (Term.list rest) (.map S) (.atom "term") []
      (Or.inl ⟨rfl, rfl, rfl⟩) (.atom "term") (inter_term_right _ _)
    have step' := (step.2 _ ((full_term ops S).2 m hm) (diff_term_right _ _)).1 (empty_none_seen _ _)
    have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D m) (.integer ([] : List Term).length)
        (.integer [Term.atom "term"].length) (.atom "open") (Term.list []) (.atom "open") (Term.list rest) (.map S) =
        .ok (.atom "true") :=
      arity_true _ _ _ _ _ _ _ (.map S) (Or.inr ⟨sizes_all _ _ _ _ _ (fun i _ lt => by
        cases i with
        | zero => exact line_closed_empty _ (.map S) rest lits' hE'
        | succ i => simp at lt) _ (Nat.le_refl _), Or.inl rfl⟩)
    simp only [Term.list] at step' arity ⊢
    rw [step', elements_done, arity]
    exact andAlso_true
  have hH' := inRest hH isH
  by_cases isE : IsE (.tuple #[.integer k, .atom tag', Term.list nl])
  · obtain ⟨rfl, rfl⟩ := notE isE
    have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D m) (.integer ([] : List Term).length)
        (.integer ([] : List Term).length) (.atom "open") (Term.list []) (.atom "closed") (Term.list rest) (.map S) =
        .ok (.atom "true") :=
      arity_true _ _ _ _ _ _ _ (.map S) (Or.inr ⟨sizes_all _ _ _ _ _ (fun i _ lt => by simp at lt) _ (Nat.le_refl _),
        Or.inr ⟨by simp, line_full ops dops hm S rest lits' hH' "open" _ (by simp) (full_fill ops S (by simp) _)⟩⟩)
    rw [elements_done, arity]
    exact andAlso_true
  have hE' := inRest hE isE
  rw [elements_all ops dops hm S (.atom "open") (Term.list rest) (fun l' ne' hl' => line_full ops dops hm S rest lits' hH' "open" l' ne' hl')
      nl hnl [] [] (by simp) (by simp),
    arity_true _ _ _ _ _ _ _ (.map S) (Or.inr ⟨sizes_all _ _ _ _ _ (closedLines hE' hH') _ (Nat.le_refl _), ?_⟩)]
  · exact andAlso_true
  by_cases o : tag' = "open"
  · exact Or.inl o
  · exact Or.inr ⟨by simp, line_full ops dops hm S rest lits' hH' "open" _ (by simp) (full_fill ops S (by simp) _)⟩

/-! Tuple BDDs that no realizable valuation satisfies are empty. -/

theorem zip_len (ops : ElemOk E K) {m : Nat} (hm : K + 1 ≤ m) (l₁ : List Term) (h₁ : ∀ e ∈ l₁, E e) :
    ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc : List Term, (∀ e ∈ acc, E e) →
    ∃ r : List Term, Elixir.Module.Types.Descr.«zip_intersection/4» (D m) (Term.list l₁) (Term.list l₂)
        (Term.list acc) (.function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) = .ok (Term.list r) ∧
      r.length = acc.length + max l₁.length l₂.length ∧ ∀ e ∈ r, E e := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  induction l₁ with
  | nil =>
    intro l₂ h₂ acc ha
    refine ⟨acc.reverse ++ l₂, ?_, by simp, fun e m => ?_⟩
    · unfold Elixir.Module.Types.Descr.«zip_intersection/4»
      exact reverse_list acc l₂
    · rcases List.mem_append.mp m with m | m
      · exact ha e (List.mem_reverse.mp m)
      · exact h₂ e m
  | cons x xs ih =>
    intro l₂ h₂ acc ha
    cases l₂ with
    | nil =>
      refine ⟨acc.reverse ++ x :: xs, ?_, by simp, fun e m => ?_⟩
      · unfold Elixir.Module.Types.Descr.«zip_intersection/4»
        exact reverse_list acc (x :: xs)
      · rcases List.mem_append.mp m with m | m
        · exact ha e (List.mem_reverse.mp m)
        · exact h₁ e m
    | cons y ys =>
      obtain ⟨e, he, run⟩ := ops.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
      obtain ⟨r, runr, len, hr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
        (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (e :: acc) (fun e' me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact he
          · exact ha e' me)
      refine ⟨r, ?_, by simp at len ⊢; omega, hr⟩
      unfold Elixir.Module.Types.Descr.«zip_intersection/4»
      simp [run n hn]
      exact runr

def Disj (t₁ t₂ : String) (n₁ n₂ : Nat) : Prop :=
  (t₁ = "closed" ∧ t₂ = "closed" ∧ n₁ ≠ n₂) ∨ (t₁ = "closed" ∧ t₂ = "open" ∧ n₁ < n₂) ∨
    (t₁ = "open" ∧ t₂ = "closed" ∧ n₂ < n₁)

theorem strategy_spec (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    (n₁ n₂ : Nat) : ∃ v, Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
      (.integer n₂) = .ok v ∧ (v = .atom "disjoint" ↔ Disj t₁ t₂ n₁ n₂) := by
  unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> rcases Nat.lt_trichotomy n₁ n₂ with h | h | h <;>
    simp [Erlang.erlang.«/=/2», Erlang.erlang.«==/2», Disj, h, Int.compare_eq_lt,
      Int.compare_eq_gt, Erlang.erlang.«>=/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Int.isGE_compare] <;>
    first | omega | (have := Nat.le_of_lt h; have := Nat.not_lt.mpr (Nat.le_of_lt h); simp [*]) |
      (have : (n₁ : Int) ≠ n₂ := by omega
       have : n₁ ≠ n₂ := by omega
       simp [*])

def IsE' (t : Term) : Prop := ∃ k, t = .tuple #[k, .atom "closed", .nil]
def IsH' (t : Term) : Prop := ∃ k, t = .tuple #[k, .atom "open", Term.list [.atom "term"]]
def Sized (t : Term) : Prop := ∃ k tag x xs, t = .tuple #[k, tag, .cons x xs]

/-- Lines known to hold only `{}`. -/
def PosE (pos : Term) : Prop := pos = .tuple #[.atom "closed", .nil]

/-- Lines known to hold only tuples with elements. -/
def PosH (pos : Term) : Prop := ∃ tag x xs, pos = .tuple #[tag, .cons x xs]

theorem inter_facts (ops : ElemOk E K) {m : Nat} (hm : K + 1 ≤ m) {pos lit : Term} (hp : TuplePos E pos)
    (hl : TupleOk E lit) :
    Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok (.atom "empty") ∨
      ∃ pos', Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok pos' ∧
        TuplePos E pos' ∧ (PosE pos → PosE pos') ∧ (PosH pos → PosH pos') ∧ (IsE' lit → PosE pos') ∧
        (Sized lit → PosH pos') := by
  obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
  obtain ⟨⟨k, t₂, l₂, rfl, g₂, e₂⟩, -⟩ := hl
  obtain ⟨v, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  obtain ⟨r, zip, len, hr⟩ := zip_len ops hm l₁ e₁ l₂ e₂ [] (by simp)
  simp only [List.length_nil, Nat.zero_add] at len
  unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
  simp only [length_list, Lynx.Except.ok_bind, hv]
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · left
    rw [disj.mpr d]
    rfl
  right
  have nv : v ≠ .atom "disjoint" := fun e => d (disj.mp e)
  let tag : String := if t₁ = "open" ∧ t₂ = "open" then "open" else "closed"
  have hr' : ∀ e ∈ r, E e := hr
  refine ⟨.tuple #[.atom tag, Term.list r], ?_, ⟨tag, r, rfl, by simp only [tag]; split <;> simp, hr'⟩, ?_⟩
  · split
    · exact absurd rfl nv
    · simp only [Term.list] at zip
      by_cases o₁ : t₁ = "open" <;> by_cases o₂ : t₂ = "open" <;>
        simp [tag, o₁, o₂, Erlang.erlang.«==/2», Lynx.Except.andAlso, zip]
  have nd : ¬Disj t₁ t₂ l₁.length l₂.length := d
  simp only [Disj, not_or, not_and] at nd
  refine ⟨fun pe => ?_, fun ⟨_, x, xs, ph⟩ => ?_, fun ⟨k', le⟩ => ?_, fun ⟨k', tg, x, xs, ls⟩ => ?_⟩
  · simp [PosE] at pe
    obtain ⟨rfl, hl₁⟩ := pe
    have : l₁ = [] := by cases l₁ <;> simp_all [Term.list]
    subst this
    have hl₂ : l₂.length = 0 := by rcases g₂ with rfl | rfl <;> simp at nd <;> first | omega | simp [nd]
    have : r = [] := List.eq_nil_of_length_eq_zero (by rw [len]; simp [hl₂])
    subst this
    simp [PosE, tag, Term.list]
  · simp at ph
    obtain ⟨-, hl₁⟩ := ph
    have : l₁ ≠ [] := by rintro rfl; simp [Term.list] at hl₁
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by
      cases r with
      | nil => simp at len; exact absurd (List.length_eq_zero_iff.mp (by omega)) this
      | cons y ys => exact ⟨y, ys, rfl⟩
    exact ⟨_, y, Term.list ys, rfl⟩
  · simp at le
    obtain ⟨-, rfl, hl₂⟩ := le
    have : l₂ = [] := by cases l₂ <;> simp_all [Term.list]
    subst this
    have hl₁ : l₁.length = 0 := by rcases g₁ with rfl | rfl <;> simp at nd <;> first | omega | simp [nd]
    have : r = [] := List.eq_nil_of_length_eq_zero (by rw [len]; simp [hl₁])
    subst this
    simp [PosE, tag, Term.list]
  · simp at ls
    obtain ⟨-, -, hl₂⟩ := ls
    have : l₂ ≠ [] := by rintro rfl; simp [Term.list] at hl₂
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by
      cases r with
      | nil => simp at len; exact absurd (List.length_eq_zero_iff.mp (by omega)) this
      | cons y ys => exact ⟨y, ys, rfl⟩
    exact ⟨_, y, Term.list ys, rfl⟩

theorem cons_cmp {x xs b : Term} (e : Term.compare (Term.fuel (.cons x xs) b) (.cons x xs) b = .eq) :
    ∃ y ys, b = .cons y ys ∧ Term.compare (Term.fuel x y) x y = .eq ∧ Term.compare (Term.fuel xs ys) xs ys = .eq := by
  cases b <;> rw [compare_step] at e <;> simp [Compare.compareStep] at e
  rename_i y ys
  exact ⟨y, ys, rfl, e.1, e.2⟩

theorem atom_cmp {name : String} {b : Term} (e : Term.compare (Term.fuel (.atom name) b) (.atom name) b = .eq) : b = .atom name :=
  (compare_eq_atom b name).mp (Lynx.Term.compare_eq_symm e)

theorem isE_cmp {t t' : Term} (h : IsE' t) (e : Term.compare (Term.fuel t t') t t' = .eq) : IsE' t' := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨b₀, b₁, b₂, rfl, -, e₁, e₂⟩ := tuple3_cmp e
  rw [atom_cmp e₁, (nil_compare_eq b₂).mp e₂]
  exact ⟨b₀, rfl⟩

theorem isH_cmp {t t' : Term} (h : IsH' t) (e : Term.compare (Term.fuel t t') t t' = .eq) : IsH' t' := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨b₀, b₁, b₂, rfl, -, e₁, e₂⟩ := tuple3_cmp e
  obtain ⟨y, ys, rfl, ey, eys⟩ := cons_cmp e₂
  rw [atom_cmp e₁, atom_cmp ey, (nil_compare_eq ys).mp eys]
  exact ⟨b₀, rfl⟩

theorem sized_cmp {t t' : Term} (h : Sized t) (e : Term.compare (Term.fuel t t') t t' = .eq) : Sized t' := by
  obtain ⟨k, tag, x, xs, rfl⟩ := h
  obtain ⟨b₀, b₁, b₂, rfl, -, -, e₂⟩ := tuple3_cmp e
  obtain ⟨y, ys, rfl, -, -⟩ := cons_cmp e₂
  exact ⟨b₀, b₁, y, ys, rfl⟩

theorem isE_not_sized {t : Term} (h : IsE' t) (s : Sized t) : False := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨_, _, _, _, e⟩ := s
  simp at e

theorem isE_not_isH {t : Term} (h : IsE' t) (s : IsH' t) : False := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨_, e⟩ := s
  simp at e

theorem isH_sized {t : Term} (h : IsH' t) : Sized t := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, _, _, _, rfl⟩

/-- Valuations of tuple literals that a tuple realizes: `{}` when `e`, otherwise a tuple with elements. -/
def Consistent (ρ : Term → Bool) (e : Bool) : Prop :=
  (∀ t, IsE' t → ρ t = e) ∧ (∀ t, IsH' t → ρ t = !e) ∧ (e = Bool.true → ∀ t, Sized t → ρ t = Bool.false)

def Real (ρ : Term → Bool) : Prop := ∃ e, Consistent ρ e

open Classical in
noncomputable def realize (e : Bool) (t : Term) : Bool :=
  if IsE' t then e else if IsH' t then !e else if e = Bool.true ∧ Sized t then Bool.false else Bool.true

theorem realize_resp (e : Bool) : Resp (realize e) := by
  intro a b h
  have h' := Lynx.Term.compare_eq_symm h
  have iE : IsE' a ↔ IsE' b := ⟨fun x => isE_cmp x h, fun x => isE_cmp x h'⟩
  have iH : IsH' a ↔ IsH' b := ⟨fun x => isH_cmp x h, fun x => isH_cmp x h'⟩
  have iS : Sized a ↔ Sized b := ⟨fun x => sized_cmp x h, fun x => sized_cmp x h'⟩
  unfold realize
  by_cases x : IsE' a
  · simp [x, iE.mp x]
  have x' : ¬IsE' b := fun y => x (iE.mpr y)
  by_cases y : IsH' a
  · simp [x, x', y, iH.mp y]
  have y' : ¬IsH' b := fun z => y (iH.mpr z)
  by_cases z : Sized a
  · simp [x, x', y, y', z, iS.mp z]
  · have z' : ¬Sized b := fun w => z (iS.mpr w)
    simp [x, x', y, y', z, z']

theorem realize_consistent (e : Bool) : Consistent (realize e) e := by
  refine ⟨fun t h => by simp [realize, h], fun t h => ?_, fun he t h => ?_⟩
  · have : ¬IsE' t := fun x => isE_not_isH x h
    simp [realize, this, h]
  · have : ¬IsE' t := fun x => isE_not_sized x h
    by_cases hh : IsH' t
    · simp [realize, this, hh, he]
    · simp [realize, this, hh, he, h]

theorem consistent_flip {ρ : Term → Bool} {e : Bool} {lit : Term} {v : Bool} (c : Consistent ρ e)
    (hE : IsE' lit → v = e) (hH : IsH' lit → v = !e) (hS : e = Bool.true → Sized lit → v = Bool.false) :
    Consistent (flip ρ lit v) e := by
  refine ⟨fun t h => ?_, fun t h => ?_, fun he t h => ?_⟩ <;> simp only [BddProofs.flip] <;> split
  · next eq => exact hE (isE_cmp h eq)
  · exact c.1 t h
  · next eq => exact hH (isH_cmp h eq)
  · exact c.2.1 t h
  · next eq => exact hS he (sized_cmp h eq)
  · exact c.2.2 he t h

/-- What the literals gathered by a line allow the realizing tuple to be: `{}` when `e`. -/
def Allowed (pos : Term) (negs : List Term) (e : Bool) : Prop :=
  (e = Bool.true → (¬∃ t ∈ negs, IsE t) ∧ ¬PosH pos) ∧ (e = Bool.false → (¬∃ t ∈ negs, IsH t) ∧ ¬PosE pos)

/-- Lines check first whether some element is empty. -/
theorem elements_check (ops : ElemOk E K) (S : List (Term × Term)) (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∃ b, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D m) (Term.list l) (.map S) =
      .ok (boolAtom b)) ∧ (b = Bool.false → ∀ e ∈ l, Full E K S e) := by
  have each : ∀ e ∈ l, ∃ b, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map S) = .ok (boolAtom b) :=
    fun e me => ops.empty (hl e me) S
  classical
  let res : Term → Bool := fun e => if h : e ∈ l then Classical.choose (each e h) else Bool.false
  have hres : ∀ e ∈ l, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map S) = .ok (boolAtom (res e)) := by
    intro e me m' h
    simp only [res, dite_eq_left me]
    exact Classical.choose_spec (each e me) m' h
  refine ⟨l.any res, fun m hm => ?_, fun no e me => ⟨hl e me, fun m' h => ?_⟩⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    simp only [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2»]
    refine any_list _ _ _ _ res l fun x mx => ?_
    rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2»]
    exact hres x mx n hn
  · have := List.any_eq_false.mp no e me
    rw [hres e me m' h]
    simp_all [boolAtom]

/-- A line that no tuple can realize is empty. -/
theorem top_case (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K + 1 ≤ m) (S : List (Term × Term)) {tag : String}
    {l : List Term} (g : tag = "open" ∨ tag = "closed") (el : ∀ e ∈ l, E e) {negs : List Term}
    (lits : ∀ t ∈ negs, TupleLit E t) (none : ∀ e, ¬Allowed (.tuple #[.atom tag, Term.list l]) negs e) :
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
  have A : (∃ t ∈ negs, IsE t) ∨ PosH (.tuple #[.atom tag, Term.list l]) := by
    refine Classical.byContradiction fun h => none Bool.true ⟨fun _ => ⟨fun x => h (Or.inl x), fun x => h (Or.inr x)⟩,
      fun e => by simp at e⟩
  have B : (∃ t ∈ negs, IsH t) ∨ PosE (.tuple #[.atom tag, Term.list l]) := by
    refine Classical.byContradiction fun h => none Bool.false ⟨fun e => by simp at e,
      fun _ => ⟨fun x => h (Or.inl x), fun x => h (Or.inr x)⟩⟩
  have posE : PosE (.tuple #[.atom tag, Term.list l]) → tag = "closed" ∧ l = [] := by
    intro e
    simp [PosE] at e
    exact ⟨e.1, by cases l <;> simp_all [Term.list]⟩
  have posH : PosH (.tuple #[.atom tag, Term.list l]) → l ≠ [] := by
    rintro ⟨_, x, xs, e⟩ rfl
    simp [Term.list] at e
  have nonempty : negs ≠ [] := by
    rintro rfl
    rcases A with ⟨t, m, -⟩ | pa
    · simp at m
    rcases B with ⟨t, m, -⟩ | pb
    · simp at m
    exact posH pa (posE pb).2
  have notNil : Erlang.erlang.«==/2» (Term.list negs) .nil = .ok (.atom "false") := by
    cases negs with
    | nil => exact absurd rfl nonempty
    | cons x xs => simp [Erlang.erlang.«==/2», Term.list, Term.false]
  simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
  rcases A with hE | pa <;> rcases B with hH | pb
  · exact line_both ops dops hm' S negs lits hE hH tag g l full
  · obtain ⟨rfl, rfl⟩ := posE pb
    exact line_closed_empty _ (.map S) negs lits hE
  · exact line_full ops dops hm' S negs lits hH tag l (posH pa) full
  · exact absurd (posE pb).2 (posH pa)

/-- No valuation that a tuple allowed by a line realizes satisfies the BDD. -/
def RealUnsat (pos : Term) (negs : List Term) (r : Term) : Prop :=
  ∀ e, Allowed pos negs e → ∀ ρ, Resp ρ → Consistent ρ e → eval ρ r = Bool.false

theorem isE_int {t : Term} (lit : TupleLit E t) (h : IsE' t) : IsE t := by
  obtain ⟨k, tag, l, rfl, -, -⟩ := lit
  obtain ⟨k', e⟩ := h
  simp at e
  obtain ⟨-, rfl, e⟩ := e
  exact ⟨k, by rw [e]⟩

theorem isH_int {t : Term} (lit : TupleLit E t) (h : IsH' t) : IsH t := by
  obtain ⟨k, tag, l, rfl, -, -⟩ := lit
  obtain ⟨k', e⟩ := h
  simp at e
  obtain ⟨-, rfl, e⟩ := e
  exact ⟨k, by rw [e]⟩

/-- Taking the positive branch of a literal keeps the valuations consistent. -/
theorem flip_pos {ρ : Term → Bool} {e : Bool} {lit pos' : Term} (c : Consistent ρ e)
    (allowed : (e = Bool.true → ¬PosH pos') ∧ (e = Bool.false → ¬PosE pos'))
    (hE : IsE' lit → PosE pos') (hS : Sized lit → PosH pos') : Consistent (flip ρ lit Bool.true) e := by
  refine consistent_flip c (fun h => ?_) (fun h => ?_) (fun he h => ?_)
  · cases e
    · exact absurd (hE h) (allowed.2 rfl)
    · rfl
  · cases e
    · rfl
    · exact absurd (hS (isH_sized h)) (allowed.1 rfl)
  · exact absurd (hS h) (allowed.1 he)

theorem flip_above {ok : Term → Prop} {lit x : Term} (wx : Bdd (Above ok lit) x) (ρ : Term → Bool) (v : Bool) :
    eval (flip ρ lit v) x = eval ρ x := by
  refine eval_ext wx fun t ht => ?_
  have : Term.compare (Term.fuel t lit) t lit ≠ .eq := fun e => by
    have := ht.2; rw [Lynx.Term.compare_eq_symm e] at this; cases this
  simp [BddProofs.flip, this]

theorem flip_self (ρ : Term → Bool) (lit : Term) (v : Bool) : flip ρ lit v lit = v := by
  simp [BddProofs.flip, Std.ReflCmp.compare_self]

theorem tuple_bdd_real (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K + 1 ≤ m) (S : List (Term × Term)) {ok : Term → Prop}
    {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos → (∀ t ∈ negs, TupleLit E t) → RealUnsat pos negs r →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos →
    (∀ t ∈ negs, TupleLit E t) → RealUnsat pos negs r →
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits g
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    simp only
    exact top_case ops dops hm S gt el lits fun e allowed => by
      have := g e allowed (realize e) (realize_resp e) (realize_consistent e)
      simp at this
  · intro ok _ pos negs _ _ _
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    split <;> simp_all
  · intro ok k x y okl okLit pos negs hp lits g
    have hl := okLit _ okl
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_facts ops hm hp hl with empty | ⟨pos', run, hp', fE, fH, lE, lS⟩
    · simp [empty]
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    simp [run]
    refine top_case ops dops hm S gt el lits fun e allowed => ?_
    have c := flip_pos (realize_consistent e) ⟨fun he => (allowed.1 he).2, fun he => (allowed.2 he).2⟩ lE lS
    have := g e ⟨fun he => ⟨(allowed.1 he).1, fun p => (allowed.1 he).2 (fH p)⟩,
      fun he => ⟨(allowed.2 he).1, fun p => (allowed.2 he).2 (fE p)⟩⟩ _ ((realize_resp e).flip _ _) c
    simp [flip_self] at this
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits g
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    have dPart : Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list (lit :: negs)) d (.map S) =
        .ok (.atom "true") := by
      refine idd okLit' pos (lit :: negs) hp (fun t m => ?_) fun e allowed ρ resp cons => ?_
      · rcases List.mem_cons.mp m with rfl | m
        · exact hl.1
        · exact lits t m
      have c' : Consistent (flip ρ lit Bool.false) e := by
        refine consistent_flip cons (fun h => ?_) (fun h => ?_) (fun _ _ => rfl)
        · cases e
          · rfl
          · exact absurd ⟨lit, List.mem_cons_self, isE_int hl.1 h⟩ (allowed.1 rfl).1
        · cases e
          · exact absurd ⟨lit, List.mem_cons_self, isH_int hl.1 h⟩ (allowed.2 rfl).1
          · rfl
      have := g e ⟨fun he => ⟨fun ⟨t, m, ht⟩ => (allowed.1 he).1 ⟨t, List.mem_cons_of_mem _ m, ht⟩, (allowed.1 he).2⟩,
        fun he => ⟨fun ⟨t, m, ht⟩ => (allowed.2 he).1 ⟨t, List.mem_cons_of_mem _ m, ht⟩, (allowed.2 he).2⟩⟩
        _ (resp.flip _ _) c'
      simp only [eval_node, flip_self, flip_above hc, flip_above hu, flip_above hd] at this
      simp at this
      exact this.2
    have uPart := iu okLit' pos negs hp lits fun e allowed ρ resp cons => by
      have := g e allowed ρ resp cons
      simp only [eval_node] at this
      cases hu' : eval ρ u
      · rfl
      · simp [hu'] at this
    rw [list_cons] at dPart
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_facts ops hm ⟨tag, l, rfl, gt, el⟩ hl with empty | ⟨pos2, run, hp2, fE, fH, lE, lS⟩
    · simp [empty, dPart, uPart, Lynx.Except.andAlso]
    have cRes := ic okLit' pos2 negs hp2 lits fun e allowed ρ resp cons => by
      have c' := flip_pos cons ⟨fun he => (allowed.1 he).2, fun he => (allowed.2 he).2⟩ lE lS
      have := g e ⟨fun he => ⟨(allowed.1 he).1, fun p => (allowed.1 he).2 (fH p)⟩,
        fun he => ⟨(allowed.2 he).1, fun p => (allowed.2 he).2 (fE p)⟩⟩ _ (resp.flip _ _) c'
      simp only [eval_node, flip_self, flip_above hc, flip_above hu, flip_above hd] at this
      simp at this
      exact this.1
    obtain ⟨tag2, l2, rfl, -⟩ := hp2
    simp [run, dPart, uPart, Lynx.Except.andAlso, cRes]

/-- Tuple BDDs that no realizable valuation satisfies are empty. -/
theorem tuple_empty_real (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K + 1 ≤ m) {ok : Term → Prop}
    (okLit : ∀ t, ok t → TupleOk E t) {r : Term} (wr : Bdd ok r)
    (unsat : ∀ ρ, Resp ρ → Real ρ → eval ρ r = Bool.false) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) r (.map []) = .ok (.atom "true") := by
  have run := tuple_bdd_real ops dops hm [(.cons (.atom "tuple") r, .atom "true")] wr okLit (.tuple #[.atom "open", .nil]) [] ⟨"open", [], rfl, Or.inl rfl, by simp⟩
    (by simp) fun e _ ρ resp cons => unsat ρ resp ⟨e, cons⟩
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.false,
    Erlang.maps.«put/3»]
  simpa [Term.list] using run

/-! Tuple types of element types decide their emptiness, whatever their lines. -/

/-- Computations returning the same Boolean at every call depth from `K`. -/
def BoolAt (K : Nat) (f : Nat → Except Exception Term) : Prop :=
  ∃ b : Bool, ∀ m, K ≤ m → f m = .ok (boolAtom b)

theorem BoolAt.mono {K K' : Nat} {f : Nat → Except Exception Term} (h : BoolAt K f) (le : K ≤ K') : BoolAt K' f :=
  let ⟨b, hb⟩ := h
  ⟨b, fun m hm => hb m (by omega)⟩

@[simp] theorem andAlso_bool (a b : Bool) :
    Lynx.Except.andAlso (.ok (boolAtom a)) (.ok (boolAtom b)) Bool.true = .ok (boolAtom (a && b)) := by
  cases a <;> cases b <;> simp [boolAtom, Lynx.Except.andAlso]

theorem BoolAt.of_eq {K : Nat} {f g : Nat → Except Exception Term} (h : ∀ m, K ≤ m → f m = g m)
    (hg : BoolAt K g) : BoolAt K f := by
  obtain ⟨b, hb⟩ := hg
  exact ⟨b, fun m hm => by rw [h m hm]; exact hb m hm⟩

theorem BoolAt.andAlso {K : Nat} {f g : Nat → Except Exception Term} (hf : BoolAt K f) (hg : BoolAt K g) :
    BoolAt K (fun m => Lynx.Except.andAlso (f m) (g m) Bool.true) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a && b, fun m hm => by dsimp only; rw [ha m hm, hb m hm, andAlso_bool]⟩

theorem line_nil (d : Dispatcher) (tag l S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d tag l .nil S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«tuple_line_empty?/4».eq_def]
  split <;> simp_all

theorem line_last (d : Dispatcher) (l : Term) (k : Int) (nl S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") l
      (.cons (.tuple #[.integer k, .atom "closed", nl]) .nil) S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«tuple_line_empty?/4».eq_def]
  split <;> simp_all

/-- Checking each element of a line against a negated literal returns a Boolean. -/
theorem elements_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) (tag rest : Term)
    (lineOk : ∀ l, (∀ e ∈ l, Full E K S e) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) tag (Term.list l) rest (.map S))) :
    ∀ nl : List Term, (∀ e ∈ nl, E e) → ∀ acc l : List Term, (∀ e ∈ acc, Full E K S e) →
      (∀ e ∈ l, Full E K S e) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_elements_empty?/6» (D m) (Term.list acc) tag
        (Term.list l) (Term.list nl) rest (.map S)) := by
  intro nl
  induction nl with
  | nil =>
    intro _ acc l _ _
    exact ⟨Bool.true, fun m _ => by simpa [Term.list, boolAtom] using elements_done (D m) _ _ _ _ _⟩
  | cons nt nl ih =>
    intro hnl acc l hacc hl
    obtain ⟨ty, es, hshape, hty, hes⟩ : ∃ ty es, ((l = [] ∧ ty = .atom "term" ∧ es = []) ∨ l = ty :: es) ∧
        Full E K S ty ∧ ∀ e ∈ es, Full E K S e := by
      cases l with
      | nil => exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, full_term ops S, by simp⟩
      | cons x xs => exact ⟨x, xs, Or.inr rfl, hl x List.mem_cons_self, fun e m => hl e (List.mem_cons_of_mem _ m)⟩
    have hnt := hnl nt List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e m => hnl e (List.mem_cons_of_mem _ m)
    obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty.1 hnt
    have step := fun m (hm : K ≤ m) =>
      elements_step (D m) acc tag l nt nl rest (.map S) ty es hshape meet (hmeet m hm)
    have allRev : ∀ x, Full E K S x → ∀ e ∈ acc.reverse ++ x :: es, Full E K S e := by
      intro x hx e m
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
      rcases m with m | rfl | m
      · exact hacc e m
      · exact hx
      · exact hes e m
    rw [list_cons]
    obtain ⟨bm, em⟩ := ops.empty lmeet S
    cases bm
    · have fullMeet : Full E K S meet := ⟨lmeet, fun m' h' => by simpa [boolAtom] using em m' h'⟩
      obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty.1 hnt
      obtain ⟨bd, ed⟩ := ops.empty ldiff S
      cases bd
      · have fullDiff : Full E K S diff := ⟨ldiff, fun m' h' => by simpa [boolAtom] using ed m' h'⟩
        obtain ⟨b, hb⟩ := (lineOk _ (allRev diff fullDiff)).andAlso
          (ih hnl' (meet :: acc) es (fun e m => by
            rcases List.mem_cons.mp m with rfl | m
            · exact fullMeet
            · exact hacc e m) hes)
        exact ⟨b, fun m hm => by
          dsimp only
          rw [((step m hm).2 _ (fullMeet.2 m hm) (hdiff m hm)).2 (fullDiff.2 m hm)]
          exact hb m hm⟩
      · obtain ⟨b, hb⟩ := ih hnl' (ty :: acc) es (fun e m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact hty
          · exact hacc e m) hes
        exact ⟨b, fun m hm => by
          dsimp only
          rw [((step m hm).2 _ (fullMeet.2 m hm) (hdiff m hm)).1 (by simpa [boolAtom] using ed m hm)]
          exact hb m hm⟩
    · obtain ⟨b, hb⟩ := lineOk _ (allRev ty hty)
      exact ⟨b, fun m hm => by dsimp only; rw [(step m hm).1 (by simpa [boolAtom] using em m hm)]; exact hb m hm⟩

/-- `tuple_empty_sizes?/5` returns a Boolean when each closed line does. -/
theorem sizes_total (S : List (Term × Term)) (l : List Term) (m' : Nat) (rest : Term)
    (lines : ∀ i, l.length ≤ i → i < m' → BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m)
      (Term.atom "closed") (Term.list (l ++ List.replicate (i - l.length) (Term.atom "term"))) rest (Term.map S))) :
    ∀ i, l.length ≤ i → BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» (D m) (.integer i)
      (.integer m') (Term.list l) rest (.map S)) := by
  intro i le
  induction h : m' - i generalizing i with
  | zero =>
    refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have : ¬(i : Int) < m' := by omega
    simp [this, boolAtom]
  | succ k ih =>
    have lt : (i : Int) < m' := by omega
    obtain ⟨b₁, h₁⟩ := lines i le (by omega)
    obtain ⟨b₂, h₂⟩ := ih (i + 1) (by omega) (by omega)
    refine ⟨b₁ && b₂, fun m hm => ?_⟩
    dsimp only
    have next := h₂ m hm
    simp only [Int.natCast_add, Int.natCast_one] at next
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    simp [lt, fill_list l i le, h₁ m hm, next]

/-- `tuple_empty_arity?/7` returns a Boolean when its sizes and larger open line do. -/
theorem arity_total (S : List (Term × Term)) (m' : Nat) (tag : String) (l : List Term) (ntag : String) (rest : Term)
    (fits : ntag = "open" ∨ tag = "closed" ∨ l.length ≤ m')
    (sizes : BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» (D m) (.integer l.length)
      (.integer m') (Term.list l) rest (.map S)))
    (big : l.length ≤ m' + 1 → BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m)
      (Term.atom "open") (Term.list (l ++ List.replicate (m' + 1 - l.length) (Term.atom "term"))) rest (Term.map S))) :
    BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D m) (.integer l.length) (.integer m')
      (.atom tag) (Term.list l) (.atom ntag) rest (.map S)) := by
  by_cases c : tag = "closed"
  · refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
    simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, boolAtom]
  obtain ⟨bs, hs⟩ := sizes
  by_cases o : ntag = "open"
  · refine ⟨bs, fun m hm => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
    cases bs <;> simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, hs m hm, Lynx.Except.andAlso, o, boolAtom]
  · have le : l.length ≤ m' + 1 := by
      rcases fits with h | h | h
      · exact absurd h o
      · exact absurd h c
      · omega
    obtain ⟨bl, hl⟩ := big le
    have fill := fill_list l (m' + 1) le
    simp only [Int.natCast_add, Int.natCast_one] at fill
    refine ⟨bs && bl, fun m hm => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
    cases bs <;> cases bl <;>
      simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c, hs m hm, Lynx.Except.andAlso, o, fill, hl m hm, boolAtom]

/-- A line of nonempty element types minus any negated literals returns a Boolean. -/
theorem line_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) :
    ∀ negs : List Term, (∀ t ∈ negs, TupleLit E t) → ∀ (tag : String) (l : List Term), (∀ e ∈ l, Full E K S e) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom tag) (Term.list l)
        (Term.list negs) (.map S)) := by
  intro negs
  induction negs with
  | nil =>
    intro _ tag l _
    exact ⟨Bool.false, fun m _ => by simpa [Term.list, boolAtom] using line_nil (D m) _ _ _⟩
  | cons N rest ih =>
    intro lits tag l hl
    obtain ⟨k, tag', nl, rfl, -, hnl⟩ := lits N List.mem_cons_self
    have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    have ih' := ih lits'
    rw [list_cons]
    by_cases top : tag' = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact ⟨Bool.true, fun m _ => by simpa [boolAtom] using line_top (D m) _ _ k _ _⟩
    by_cases last : tag = "open" ∧ tag' = "closed" ∧ rest = []
    · obtain ⟨rfl, rfl, rfl⟩ := last
      exact ⟨Bool.false, fun m _ => by simpa [boolAtom, Term.list] using line_last (D m) _ k _ _⟩
    have hcons := fun m => line_cons (D m) tag l k tag' nl rest (.map S) top last
    by_cases cond : (tag = "closed" ∧ l.length < nl.length) ∨ (tag' = "closed" ∧ nl.length < l.length)
    · obtain ⟨b, hb⟩ := ih' tag l hl
      exact ⟨b, fun m hm => by dsimp only; rw [hcons m, ite_eq_left_of_eq_true _ _ (eq_true cond)]; exact hb m hm⟩
    · have elems := elements_total ops dops S (.atom tag) (Term.list rest) (fun l' hl' => ih' tag l' hl') nl hnl
        [] l (by simp) hl
      have arity := arity_total S nl.length tag l tag' (Term.list rest)
        (by
          by_cases o : tag' = "open"
          · exact Or.inl o
          by_cases c : tag = "closed"
          · exact Or.inr (Or.inl c)
          · refine Or.inr (Or.inr ?_)
            have closed : tag' = "closed" := by
              rcases lits _ List.mem_cons_self with ⟨_, _, _, e, g, -⟩
              simp at e; obtain ⟨-, rfl, -⟩ := e; rcases g with g | g <;> simp_all
            simp only [closed, true_and, not_or] at cond
            omega)
        (sizes_total S l nl.length (Term.list rest)
          (fun i _ _ => ih' "closed" _ (full_fill ops S hl _)) l.length (Nat.le_refl _))
        (fun _ => ih' "open" _ (full_fill ops S hl _))
      obtain ⟨b, hb⟩ := elems.andAlso arity
      exact ⟨b, fun m hm => by dsimp only; rw [hcons m, ite_eq_right_of_eq_false _ _ (eq_false cond)]; exact hb m hm⟩

/-- Lines of element types return a Boolean, whether or not some element is empty. -/
theorem line_seen_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {tag : String}
    {l : List Term} (el : ∀ e ∈ l, E e) {negs : List Term} (lits : ∀ t ∈ negs, TupleLit E t) :
    BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4» (D m) (.atom tag) (Term.list l)
      (Term.list negs) (.map S)) := by
  obtain ⟨b, check, full⟩ := elements_check ops S l el
  cases b
  · cases negs with
    | nil =>
      refine ⟨Bool.false, fun m hm => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
      simp [check m hm, boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, Term.list,
        Erlang.erlang.«==/2»]
    | cons N rest =>
      obtain ⟨b, hb⟩ := line_total ops dops S (N :: rest) lits tag l (full rfl)
      refine ⟨b, fun m hm => ?_⟩
      dsimp only
      have notNil : Erlang.erlang.«==/2» (Term.list (N :: rest)) .nil = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2», Term.list, Term.false]
      rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
      simp [check m hm, boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
      simpa [boolAtom] using hb m (by omega)
  · refine ⟨Bool.true, fun m hm => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
    simp [check m hm, boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso]

/-- Tuple BDDs of element types return a Boolean along every path. -/
theorem tuple_bdd_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {ok : Term → Prop}
    {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → TupleLit E t) → ∀ pos negs, TuplePos E pos → (∀ t ∈ negs, TupleLit E t) →
      BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r
        (.map S)) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit E t) → ∀ pos negs, TuplePos E pos →
    (∀ t ∈ negs, TupleLit E t) →
    BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S)))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits
    obtain ⟨tag, l, rfl, -, el⟩ := hp
    obtain ⟨b, hb⟩ := line_seen_total (tag := tag) ops dops S el lits
    refine ⟨b, fun m hm => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    exact hb m hm
  · intro ok _ pos negs _ _
    refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    split <;> simp_all [boolAtom]
  · intro ok k x y okl okLit pos negs hp lits
    rcases line_ok ops hp (okLit _ okl) with empty | ⟨pos', hp', run⟩
    · refine ⟨Bool.true, fun m hm => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
      simp [empty m hm, boolAtom]
    · obtain ⟨tag, l, rfl, -, el⟩ := hp'
      obtain ⟨b, hb⟩ := line_seen_total (tag := tag) ops dops S el lits
      refine ⟨b, fun m hm => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
      simp [run m hm]
      exact hb m hm
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits
    have okLit' : ∀ t, Above ok lit t → TupleLit E t := fun t ht => okLit t ht.1
    have hl := okLit _ okl
    obtain ⟨bd, hbd⟩ := idd okLit' pos (lit :: negs) hp (fun t m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hl
      · exact lits t m)
    obtain ⟨bu, hbu⟩ := iu okLit' pos negs hp lits
    rcases line_ok ops hp hl with empty | ⟨pos', hp', run⟩
    · refine ⟨bd && bu, fun m hm => ?_⟩
      dsimp only
      have dPart := hbd m hm
      rw [list_cons] at dPart
      obtain ⟨tag, l, rfl, -⟩ := hp
      rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
      cases bd <;> cases bu <;> simp [empty m hm, dPart, hbu m hm, Lynx.Except.andAlso, boolAtom]
    · obtain ⟨bc, hbc⟩ := ic okLit' pos' negs hp' lits
      refine ⟨bd && bc && bu, fun m hm => ?_⟩
      dsimp only
      have dPart := hbd m hm
      rw [list_cons] at dPart
      obtain ⟨tag, l, rfl, -⟩ := hp
      obtain ⟨tag2, l2, rfl, -⟩ := hp'
      rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
      cases bd <;> cases bc <;> cases bu <;>
        simp [run m hm, dPart, hbu m hm, hbc m hm, Lynx.Except.andAlso, boolAtom]

/-- Tuple types of element types decide their emptiness at every call depth from `K + 1`. -/
theorem tuple_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {w : Term}
    (field : TupleField E w) :
    BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) w (.map S)) := by
  have wl : Bdd (TupleLit E) w := by
    rcases field with ⟨k, rfl⟩ | wx
    · exact Bdd.leaf_iff.mpr ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
    · exact wx.mono fun _ h => h.1
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") w) e.1) (.cons (.atom "tuple") w) e.1 == .eq) = Bool.true
  · refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true, boolAtom]
  · have fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") w) e.1) (.cons (.atom "tuple") w) e.1 == .eq) = Bool.false := by
      simpa using seen
    obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "tuple") w) (.atom "true") (.map S) =
        .ok (.map S') := by
      simp [Erlang.maps.«put/3»]
    obtain ⟨b, hb⟩ := tuple_bdd_total ops dops S' wl (fun _ h => h) (.tuple #[.atom "open", .nil]) []
      ⟨"open", [], rfl, Or.inl rfl, by simp⟩ (by simp)
    refine ⟨b, fun m hm => ?_⟩
    dsimp only
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put]
    simpa [Term.list] using hb m hm

/-! Map types of element types decide their emptiness, whatever their lines. -/

/-- Computations returning the same Boolean, or throwing `:closed`, at every call depth from `K`. -/
def MeetAt (K : Nat) (f : Nat → Except Exception Term) : Prop :=
  (∃ b : Bool, ∀ m, K ≤ m → f m = .ok (boolAtom b)) ∨
    ∀ m, K ≤ m → f m = .error (Exception.throw (.atom "closed"))

theorem fieldsTerm_cons (x : Term × Term) (l : List (Term × Term)) :
    fieldsTerm (x :: l) = .cons (.tuple #[x.1, x.2]) (fieldsTerm l) := rfl

theorem reverse_fields (acc t : List (Term × Term)) :
    Erlang.lists.«reverse/2» (fieldsTerm acc) (fieldsTerm t) = .ok (fieldsTerm (acc.reverse ++ t)) := by
  have := reverse_list (acc.map fun e => .tuple #[e.1, e.2]) (t.map fun e => .tuple #[e.1, e.2])
  simpa [fieldsTerm, List.map_reverse] using this

theorem fields_append {a b : List (Term × Term)} (ha : ∀ e ∈ a, FieldValue E e.2)
    (hb : ∀ e ∈ b, FieldValue E e.2) : ∀ e ∈ a.reverse ++ b, FieldValue E e.2 := by
  intro e m
  rcases List.mem_append.mp m with m | m
  · exact ha e (List.mem_reverse.mp m)
  · exact hb e m

@[simp] theorem not_boolAtom (b : Bool) : Erlang.erlang.«not/1» (boolAtom b) = .ok (boolAtom !b) := by
  cases b <;> rfl

/-- `field_empty_seen?/3` of an element type returns a Boolean. -/
theorem field_empty_total (ops : ElemOk E K) (S : List (Term × Term)) {t : Term} (ht : E t) (o : Bool) :
    ∃ b, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«field_empty_seen?/3» (D m) t (boolAtom o) (.map S) =
      .ok (boolAtom b)) := by
  cases o
  · obtain ⟨b, hb⟩ := ops.empty ht S
    exact ⟨b, fun m hm => by
      rw [Elixir.Module.Types.Descr.«field_empty_seen?/3».eq_def]
      simpa [boolAtom] using hb m hm⟩
  · exact ⟨Bool.false, fun m _ => by
      rw [Elixir.Module.Types.Descr.«field_empty_seen?/3».eq_def]
      simp [boolAtom]⟩

/-- One field of `map_line_meet_empty?/10`. -/
theorem meet_field_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) (tag neg_tag : Term)
    (negs : Term) (key : Term) {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂)
    (t₁ t₂ : Term) (t₁' : List (Term × Term)) (ht₁ : t₁ = fieldsTerm t₁') (ft₁ : ∀ e ∈ t₁', FieldValue E e.2)
    (acc : List (Term × Term)) (hacc : ∀ e ∈ acc, FieldValue E e.2)
    (lineOk : ∀ l, (∀ e ∈ l, FieldValue E e.2) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) negs (.map S)))
    (rec : ∀ acc : List (Term × Term), (∀ e ∈ acc, FieldValue E e.2) →
      MeetAt K (fun m => Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) t₁ t₂ tag neg_tag
        (fieldsTerm acc) negs (.map S))) :
    MeetAt K (fun m => Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) key f₁ f₂ t₁ t₂ tag neg_tag
      (fieldsTerm acc) negs (.map S)) := by
  subst ht₁
  obtain ⟨ty, o₁, rfl, hty⟩ := h₁
  obtain ⟨nt, o₂, rfl, hnt⟩ := h₂
  obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty hnt
  obtain ⟨bm, em⟩ := field_empty_total ops S lmeet (o₁ && o₂)
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty hnt
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  have newAcc : ∀ e ∈ (key, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc, FieldValue E e.2 :=
    fields_cons (x := (key, .tuple #[meet, boolAtom (o₁ && o₂)])) ⟨meet, _, rfl, lmeet⟩ hacc
  have unfold10 : ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«map_line_meet_empty?/10» (D m) key (.tuple #[ty, boolAtom o₁])
        (.tuple #[nt, boolAtom o₂]) (fieldsTerm t₁') t₂ tag neg_tag (fieldsTerm acc) negs (.map S) =
      if bm then Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag
        (fieldsTerm (acc.reverse ++ (key, Term.tuple #[ty, boolAtom o₁]) :: t₁')) negs (Term.map S)
      else if bd then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁') t₂ tag neg_tag
        (fieldsTerm ((key, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc)) negs (.map S)
      else Lynx.Except.andAlso (Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag
          (fieldsTerm (acc.reverse ++ (key, Term.tuple #[diff, boolAtom (o₁ && !o₂)]) :: t₁')) negs (Term.map S))
        (Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm t₁') t₂ tag neg_tag
          (fieldsTerm ((key, .tuple #[meet, boolAtom (o₁ && o₂)]) :: acc)) negs (.map S)) Bool.true := by
    intro m hm
    have e₁ := em m hm
    have e₂ := ed m hm
    have i₁ := hmeet m hm
    have d₁ := hdiff m hm
    have revD := reverse_fields acc ((key, .tuple #[diff, boolAtom (o₁ && !o₂)]) :: t₁')
    have revT := reverse_fields acc ((key, .tuple #[ty, boolAtom o₁]) :: t₁')
    have bt : boolAtom Bool.true = .atom "true" := rfl
    have bf : boolAtom Bool.false = .atom "false" := rfl
    simp only [fieldsTerm_cons] at revD revT ⊢
    rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/10».eq_def]
    cases bm <;> cases bd <;> simp [e₁, e₂, i₁, d₁, revD, revT, isMember, bt, bf]
  cases bm
  · cases bd
    · obtain ⟨bl, hl⟩ := lineOk _ (fields_append hacc
        (fields_cons (x := (key, .tuple #[diff, boolAtom (o₁ && !o₂)])) ⟨diff, _, rfl, ldiff⟩ ft₁))
      cases bl
      · refine Or.inl ⟨Bool.false, fun m hm => ?_⟩
        dsimp only
        rw [unfold10 m hm]
        simp only [Bool.false_eq_true, ite_false]
        have hlm := hl m hm
        dsimp only at hlm
        rw [hlm]
        simp [boolAtom, Lynx.Except.andAlso]
      · rcases rec _ newAcc with ⟨br, hr⟩ | hr
        · refine Or.inl ⟨br, fun m hm => ?_⟩
          dsimp only
          rw [unfold10 m hm]
          simp only [Bool.false_eq_true, ite_false]
          have hlm := hl m hm
          have hrm := hr m hm
          dsimp only at hlm hrm
          rw [hlm, hrm]
          simp [boolAtom, Lynx.Except.andAlso]
        · refine Or.inr fun m hm => ?_
          dsimp only
          rw [unfold10 m hm]
          simp only [Bool.false_eq_true, ite_false]
          have hlm := hl m hm
          have hrm := hr m hm
          dsimp only at hlm hrm
          rw [hlm, hrm]
          simp [boolAtom, Lynx.Except.andAlso]
    · rcases rec _ newAcc with ⟨br, hr⟩ | hr
      · exact Or.inl ⟨br, fun m hm => by dsimp only; rw [unfold10 m hm]; simpa using hr m hm⟩
      · exact Or.inr fun m hm => by dsimp only; rw [unfold10 m hm]; simpa using hr m hm
  · obtain ⟨bl, hl⟩ := lineOk _ (fields_append hacc
      (fields_cons (x := (key, .tuple #[ty, boolAtom o₁])) ⟨ty, o₁, rfl, hty⟩ ft₁))
    exact Or.inl ⟨bl, fun m hm => by dsimp only; rw [unfold10 m hm]; simpa using hl m hm⟩

theorem MeetAt.of_eq {K : Nat} {f g : Nat → Except Exception Term} (h : ∀ m, K ≤ m → f m = g m)
    (hg : MeetAt K g) : MeetAt K f := by
  rcases hg with ⟨b, hb⟩ | hb
  · exact Or.inl ⟨b, fun m hm => by rw [h m hm]; exact hb m hm⟩
  · exact Or.inr fun m hm => by rw [h m hm]; exact hb m hm

theorem tag_field (tag : String) (tags : tag = "open" ∨ tag = "closed") :
    Elixir.Module.Types.Descr.«map_key_tag_to_field/1» (.atom tag) =
      .ok (.tuple #[if tag = "open" then .atom "term" else .map [], .atom "true"]) := by
  rcases tags with rfl | rfl <;> rfl

theorem tag_eq_false {T : Term} {s : String} (h : T ≠ .atom s) :
    Erlang.erlang.«==/2» T (.atom s) = .ok (.atom "false") := by
  simp [Erlang.erlang.«==/2», h, Term.false]

/-- `map_line_meet_empty?/7` returns a Boolean or throws `:closed`. -/
theorem meet_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {tag neg_tag : Term}
    (gt : MapTag E tag) (gn : MapTag E neg_tag) (negs : Term)
    (lineOk : ∀ l, (∀ e ∈ l, FieldValue E e.2) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) negs (.map S))) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) →
      (∀ e ∈ l₂, FieldValue E e.2) → ∀ acc : List (Term × Term), (∀ e ∈ acc, FieldValue E e.2) →
      MeetAt K (fun m => Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        tag neg_tag (fieldsTerm acc) negs (.map S)) := by
  obtain ⟨d₁, run₁, fd₁⟩ := tag_field_ok ops.term ops.none gt
  obtain ⟨d₂, run₂, fd₂⟩ := tag_field_ok ops.term ops.none gn
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂ acc hacc
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    refine Or.inl ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
    simp [fieldsTerm, Term.list, boolAtom]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂ acc hacc
    match l₁, l₂ with
    | [], [] =>
      refine Or.inl ⟨Bool.true, fun m _ => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
      simp [fieldsTerm, Term.list, boolAtom]
    | (k₁, f₁) :: xs, [] =>
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have r := meet_field_total ops dops S tag neg_tag negs k₁ (h₁ _ List.mem_cons_self) fd₂
        (fieldsTerm xs) (fieldsTerm []) xs rfl hxs acc hacc lineOk
        (fun acc hacc => ih xs [] (by simp at size ⊢; omega) hxs (by simp) acc hacc)
      refine r.of_eq fun m _ => ?_
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
      simp [fieldsTerm, Term.list, run₂]
    | [], (k₂, f₂) :: ys =>
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      have r := meet_field_total ops dops S tag neg_tag negs k₂ fd₁ (h₂ _ List.mem_cons_self)
        (fieldsTerm []) (fieldsTerm ys) [] rfl (by simp) acc hacc lineOk
        (fun acc hacc => ih [] ys (by simp at size ⊢; omega) (by simp) hys acc hacc)
      refine r.of_eq fun m _ => ?_
      rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
      simp [fieldsTerm, Term.list, run₁]
    | (k₁, f₁) :: xs, (k₂, f₂) :: ys =>
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁ _ List.mem_cons_self
      obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂ _ List.mem_cons_self
      have fv₁ : FieldValue E (.tuple #[t₁, boolAtom o₁]) := ⟨t₁, o₁, rfl, ht₁⟩
      have fv₂ : FieldValue E (.tuple #[t₂, boolAtom o₂]) := ⟨t₂, o₂, rfl, ht₂⟩
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel k₁ k₂) k₁ k₂
      · by_cases no : neg_tag = .atom "open"
        · subst no
          have r := ih xs ((k₂, .tuple #[t₂, boolAtom o₂]) :: ys) (by simp; omega) hxs h₂
            ((k₁, .tuple #[t₁, boolAtom o₁]) :: acc) (fields_cons fv₁ hacc)
          refine r.of_eq fun m _ => ?_
          rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp]
        by_cases nc : neg_tag = .atom "closed"
        · subst nc
          cases o₁
          · refine Or.inr fun m _ => ?_
            dsimp only
            rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1»]
          · have r := meet_field_total ops dops S tag (.atom "closed") negs k₁ fv₁ fd₂ (fieldsTerm xs)
              (fieldsTerm ((k₂, .tuple #[t₂, boolAtom o₂]) :: ys)) xs rfl hxs acc hacc lineOk
              (fun acc hacc => ih xs _ (by simp; omega) hxs h₂ acc hacc)
            refine r.of_eq fun m _ => ?_
            rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1», run₂]
        · have r := meet_field_total ops dops S tag neg_tag negs k₁ fv₁ fd₂ (fieldsTerm xs)
            (fieldsTerm ((k₂, .tuple #[t₂, boolAtom o₂]) :: ys)) xs rfl hxs acc hacc lineOk
            (fun acc hacc => ih xs _ (by simp; omega) hxs h₂ acc hacc)
          refine r.of_eq fun m _ => ?_
          rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no,
            tag_eq_false nc, Lynx.Except.andAlso, run₂]
      · have r := meet_field_total ops dops S tag neg_tag negs k₁ fv₁ fv₂ (fieldsTerm xs)
          (fieldsTerm ys) xs rfl hxs acc hacc lineOk (fun acc hacc => ih xs ys (by omega) hxs hys acc hacc)
        refine r.of_eq fun m _ => ?_
        rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
      · by_cases tc : tag = .atom "closed"
        · subst tc
          cases o₂
          · refine Or.inr fun m _ => ?_
            dsimp only
            rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1»]
          · have r := meet_field_total ops dops S (.atom "closed") neg_tag negs k₂ fd₁ fv₂
              (fieldsTerm ((k₁, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys) _ rfl h₁ acc hacc lineOk
              (fun acc hacc => ih _ ys (by simp; omega) h₁ hys acc hacc)
            refine r.of_eq fun m _ => ?_
            rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1», run₁]
        · have r := meet_field_total ops dops S tag neg_tag negs k₂ fd₁ fv₂
            (fieldsTerm ((k₁, .tuple #[t₁, boolAtom o₁]) :: xs)) (fieldsTerm ys) _ rfl h₁ acc hacc lineOk
            (fun acc hacc => ih _ ys (by simp; omega) h₁ hys acc hacc)
          refine r.of_eq fun m _ => ?_
          rw [Elixir.Module.Types.Descr.«map_line_meet_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            tag_eq_false tc, Lynx.Except.andAlso, run₁]

theorem MeetAt.andAlso {K : Nat} {f g : Nat → Except Exception Term} (hf : BoolAt K f) (hg : MeetAt K g) :
    MeetAt K (fun m => Lynx.Except.andAlso (f m) (g m) Bool.true) := by
  obtain ⟨b, hb⟩ := hf
  cases b
  · exact Or.inl ⟨Bool.false, fun m hm => by simp [hb m hm, boolAtom, Lynx.Except.andAlso]⟩
  · rcases hg with ⟨c, hc⟩ | hc
    · exact Or.inl ⟨c, fun m hm => by simp [hb m hm, hc m hm, boolAtom, Lynx.Except.andAlso]⟩
    · exact Or.inr fun m hm => by simp [hb m hm, hc m hm, boolAtom, Lynx.Except.andAlso]

/-- `orddict:store/3` keeps fields. -/
theorem store_total (key f : Term) (hf : FieldValue E f) : ∀ l : List (Term × Term), (∀ e ∈ l, FieldValue E e.2) →
    ∃ l' : List (Term × Term), Erlang.orddict.«store/3» key f (fieldsTerm l) = .ok (fieldsTerm l') ∧
      ∀ e ∈ l', FieldValue E e.2
  | [], _ => ⟨[(key, f)], by rw [Erlang.orddict.«store/3».eq_def]; simp [fieldsTerm, Term.list],
      fun e me => by rw [List.mem_singleton.mp me]; exact hf⟩
  | (k, v) :: t, hl => by
    have ht : ∀ e ∈ t, FieldValue E e.2 := fun e me => hl e (List.mem_cons_of_mem _ me)
    rcases cmp : Term.compare (Term.fuel key k) key k
    · exact ⟨(key, f) :: (k, v) :: t, by
        rw [Erlang.orddict.«store/3».eq_def]; simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp],
        fields_cons hf hl⟩
    · exact ⟨(key, f) :: t, by
        rw [Erlang.orddict.«store/3».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp],
        fields_cons hf ht⟩
    · obtain ⟨l', run, hl'⟩ := store_total key f hf t ht
      refine ⟨(k, v) :: l', ?_, fields_cons (hl _ List.mem_cons_self) hl'⟩
      have r := run
      simp only [fieldsTerm] at r
      rw [Erlang.orddict.«store/3».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, r]

/-- `map_line_fields_empty_recur?/7` returns a Boolean: the field difference is empty, or the line with it is. -/
theorem recur_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) (tag key negs : Term)
    {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) (fields : List (Term × Term))
    (hfs : ∀ e ∈ fields, FieldValue E e.2)
    (lineOk : ∀ l, (∀ e ∈ l, FieldValue E e.2) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) negs (.map S))) :
    BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7» (D m) key f₁ f₂ tag
      (fieldsTerm fields) negs (.map S)) := by
  obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂
  obtain ⟨diff, ldiff, hdiff⟩ := dops.diff ht₁ ht₂
  obtain ⟨bd, ed⟩ := field_empty_total ops S ldiff (o₁ && !o₂)
  obtain ⟨l', store, hl'⟩ := store_total key (.tuple #[diff, boolAtom (o₁ && !o₂)]) ⟨diff, _, rfl, ldiff⟩ fields hfs
  obtain ⟨bl, hbl⟩ := lineOk l' hl'
  refine ⟨bd || bl, fun m hm => ?_⟩
  have hb := hbl m hm
  dsimp only at hb ⊢
  have flag : Lynx.Except.andAlso (pure (boolAtom o₁)) (Erlang.erlang.«not/1» (boolAtom o₂)) Bool.true =
      .ok (boolAtom (o₁ && !o₂)) := by
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  have e := ed m hm
  generalize (o₁ && !o₂) = od at e store flag
  rw [Elixir.Module.Types.Descr.«map_line_fields_empty_recur?/7».eq_def]
  simp only [hdiff m hm, flag]
  simp [e, store, hb]
  cases bd <;> cases bl <;> simp [boolAtom, Lynx.Except.orElse]

/-- The fields left on one side of a field walk meet the default field of the other side. -/
theorem pos_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) (tag negs : Term) {d : Term}
    (fd : FieldValue E d) (fields : List (Term × Term)) (hfs : ∀ e ∈ fields, FieldValue E e.2)
    (lineOk : ∀ l, (∀ e ∈ l, FieldValue E e.2) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) negs (.map S))) :
    ∀ l : List (Term × Term), (∀ e ∈ l, FieldValue E e.2) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm l) d tag
        (fieldsTerm fields) negs (.map S)) ∧
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm l) d tag
        (fieldsTerm fields) negs (.map S))
  | [], _ => ⟨⟨Bool.true, fun m _ => by
        dsimp only; rw [Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6».eq_def]; simp [fieldsTerm, Term.list, boolAtom]⟩,
      ⟨Bool.true, fun m _ => by
        dsimp only; rw [Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6».eq_def]; simp [fieldsTerm, Term.list, boolAtom]⟩⟩
  | (k, f) :: t, hl => by
    have ht : ∀ e ∈ t, FieldValue E e.2 := fun e me => hl e (List.mem_cons_of_mem _ me)
    have hf : FieldValue E f := hl _ List.mem_cons_self
    obtain ⟨p, n⟩ := pos_total ops dops S tag negs fd fields hfs lineOk t ht
    refine ⟨(BoolAt.andAlso (recur_total ops dops S tag k negs hf fd fields hfs lineOk) p).of_eq fun m _ => ?_,
      (BoolAt.andAlso (recur_total ops dops S tag k negs fd hf fields hfs lineOk) n).of_eq fun m _ => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6».eq_def]; simp [fieldsTerm, Term.list]
    · rw [Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6».eq_def]; simp [fieldsTerm, Term.list]

/-- `map_line_fields_empty?/7` returns a Boolean or throws `:closed`. -/
theorem fields_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {tag neg_tag : Term}
    (gt : MapTag E tag) (gn : MapTag E neg_tag) (negs : Term) (fields : List (Term × Term))
    (hfs : ∀ e ∈ fields, FieldValue E e.2)
    (lineOk : ∀ l, (∀ e ∈ l, FieldValue E e.2) →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l) negs (.map S))) :
    ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) →
      (∀ e ∈ l₂, FieldValue E e.2) →
      MeetAt K (fun m => Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        tag neg_tag (fieldsTerm fields) negs (.map S)) := by
  obtain ⟨d₁, run₁, fd₁⟩ := tag_field_ok ops.term ops.none gt
  obtain ⟨d₂, run₂, fd₂⟩ := tag_field_ok ops.term ops.none gn
  have recur := fun key {f₁ f₂ : Term} (h₁ : FieldValue E f₁) (h₂ : FieldValue E f₂) =>
    recur_total ops dops S tag key negs h₁ h₂ fields hfs lineOk
  have tails : ∀ l₁ l₂ : List (Term × Term), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      (l₁ = [] ∨ l₂ = []) →
      MeetAt K (fun m => Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l₁) (fieldsTerm l₂)
        tag neg_tag (fieldsTerm fields) negs (.map S)) := by
    intro l₁ l₂ h₁ h₂ empty
    have both := BoolAt.andAlso (pos_total ops dops S tag negs fd₂ fields hfs lineOk l₁ h₁).1
      (pos_total ops dops S tag negs fd₁ fields hfs lineOk l₂ h₂).2
    have both' : MeetAt K (fun m => Lynx.Except.andAlso
        (Elixir.Module.Types.Descr.«map_line_fields_pos_empty?/6» (D m) (fieldsTerm l₁) d₂ tag (fieldsTerm fields)
          negs (.map S))
        (Elixir.Module.Types.Descr.«map_line_fields_neg_empty?/6» (D m) (fieldsTerm l₂) d₁ tag (fieldsTerm fields)
          negs (.map S)) Bool.true) := Or.inl both
    refine both'.of_eq fun m _ => ?_
    rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
    rcases empty with rfl | rfl
    · cases l₂ <;> simp [fieldsTerm, Term.list, run₁, run₂]
    · cases l₁ <;> simp [fieldsTerm, Term.list, run₁, run₂]
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact tails l₁ l₂ h₁ h₂ (Or.inl this)
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tails [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tails _ [] h₁ h₂ (Or.inr rfl)
    | (k₁, f₁) :: xs, (k₂, f₂) :: ys =>
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      obtain ⟨t₁, o₁, rfl, ht₁⟩ := h₁ _ List.mem_cons_self
      obtain ⟨t₂, o₂, rfl, ht₂⟩ := h₂ _ List.mem_cons_self
      have fv₁ : FieldValue E (.tuple #[t₁, boolAtom o₁]) := ⟨t₁, o₁, rfl, ht₁⟩
      have fv₂ : FieldValue E (.tuple #[t₂, boolAtom o₂]) := ⟨t₂, o₂, rfl, ht₂⟩
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel k₁ k₂) k₁ k₂
      · by_cases no : neg_tag = .atom "open"
        · subst no
          refine (ih xs ((k₂, .tuple #[t₂, boolAtom o₂]) :: ys) (by simp; omega) hxs h₂).of_eq fun m _ => ?_
          rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp]
        by_cases nc : neg_tag = .atom "closed"
        · subst nc
          cases o₁
          · refine Or.inr fun m _ => ?_
            dsimp only
            rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1»]
          · refine (MeetAt.andAlso (recur k₁ fv₁ fd₂)
              (ih xs ((k₂, .tuple #[t₂, boolAtom o₂]) :: ys) (by simp; omega) hxs h₂)).of_eq fun m _ => ?_
            rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», cmp, boolAtom,
              Lynx.Except.andAlso, Erlang.erlang.«not/1», run₂]
        · refine (MeetAt.andAlso (recur k₁ fv₁ fd₂)
            (ih xs ((k₂, .tuple #[t₂, boolAtom o₂]) :: ys) (by simp; omega) hxs h₂)).of_eq fun m _ => ?_
          rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp, tag_eq_false no,
            tag_eq_false nc, Lynx.Except.andAlso, run₂]
      · refine (MeetAt.andAlso (recur k₁ fv₁ fv₂) (ih xs ys (by omega) hxs hys)).of_eq fun m _ => ?_
        rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
      · by_cases tc : tag = .atom "closed"
        · subst tc
          cases o₂
          · refine Or.inr fun m _ => ?_
            dsimp only
            rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember]
          · refine (ih ((k₁, .tuple #[t₁, boolAtom o₁]) :: xs) ys (by simp; omega) h₁ hys).of_eq fun m _ => ?_
            rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember]
        · refine (MeetAt.andAlso (recur k₂ fd₁ fv₂)
            (ih ((k₁, .tuple #[t₁, boolAtom o₁]) :: xs) ys (by simp; omega) h₁ hys)).of_eq fun m _ => ?_
          rw [Elixir.Module.Types.Descr.«map_line_fields_empty?/7».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            tag_eq_false tc, run₁]

/-- `lists:all/2` of a closure that answers a Boolean on every element at call depths from `K`, which it runs one
level deeper. -/
theorem all_bool {K : Nat} (mo nm : String) (caps : Array Term) (l : List Term)
    (body : Nat → Term → Except Exception Term)
    (call : ∀ m x, Lynx.Dispatcher.pure (D (m + 1)) (.function mo nm 1 caps) #[x] = body m x)
    (each : ∀ x ∈ l, ∃ b : Bool, ∀ m, K ≤ m → body m x = .ok (boolAtom b)) :
    BoolAt (K + 1) (fun m => Erlang.lists.«all/2» (D m) (.function mo nm 1 caps) (Term.list l)) := by
  classical
  let res : Term → Bool := fun x => if h : x ∈ l then Classical.choose (each x h) else Bool.false
  refine ⟨l.all res, fun m hm => ?_⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  exact all_list _ _ _ _ res l fun x mx => by
    rw [call n x]
    simp only [res, dite_eq_left mx]
    exact Classical.choose_spec (each x mx) n hn

/-- `map_check_domain_keys?/3` returns a Boolean, unless an open literal meets a closed negation, which
`map_line_empty?/4` skips before checking domains. -/
theorem check_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {tag ntag : Term}
    (gt : MapTag E tag) (gn : MapTag E ntag) (skip : ¬(tag = .atom "open" ∧ ntag = .atom "closed")) :
    BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«map_check_domain_keys?/3» (D m) tag ntag (.map S)) := by
  have sub : ∀ {a b}, E a → E b → ∃ s : Bool, ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype_seen?/3» (D m) a b (.map S) = .ok (boolAtom s) := by
    intro a b ha hb
    obtain ⟨c, hc, run⟩ := dops.diff ha hb
    obtain ⟨s, hs⟩ := ops.empty hc S
    exact ⟨s, fun m hm => by simp [Elixir.Module.Types.Descr.«subtype_seen?/3», run m hm, hs m hm]⟩
  by_cases tc : tag = .atom "closed"
  · subst tc
    exact ⟨Bool.true, fun m _ => by dsimp only; rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]; rfl⟩
  by_cases no : ntag = .atom "open"
  · subst no
    exact ⟨Bool.true, fun m _ => by
      dsimp only; rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]; split <;> simp_all [boolAtom]⟩
  rcases gt with rfl | rfl | ⟨dl, rfl, hdl⟩
  · rcases gn with rfl | rfl | ⟨nl, rfl, hnl⟩
    · exact absurd rfl no
    · exact absurd ⟨rfl, rfl⟩ skip
    · obtain ⟨b, hb⟩ := all_bool (K := K) "Elixir.Module.Types.Descr" "-map_check_domain_keys?/3-fun-0-" #[.map S]
        (nl.map fun e => .tuple #[e.1, e.2])
        (fun m x => Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-0-/2» (D m) (.map S) x)
        (fun m x => by simp)
        (fun x mx => by
          obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
          obtain ⟨s, hs⟩ := sub ops.term (hnl e me)
          exact ⟨s, fun m hm => by simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-0-/2», hs m hm]⟩)
      refine ⟨(nl.length == 12) && b, fun m hm => ?_⟩
      have all := hb m hm
      have len := length_list (nl.map fun e => .tuple #[e.1, e.2])
      dsimp only
      by_cases twelve : nl.length = 12
      · cases nl with
        | nil => simp at twelve
        | cons e t =>
          rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
          simp_all [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, Term.true, boolAtom]
      · have ne : (nl.length : Int) ≠ 12 := by omega
        cases nl with
        | nil =>
          rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
          simp [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, Term.false, boolAtom,
            Erlang.erlang.«length/1»]
        | cons e t =>
          rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
          simp_all [fieldsTerm, Term.list, Erlang.erlang.«==/2», Lynx.Except.andAlso, Term.false, boolAtom]
  · exact absurd rfl tc
  · rcases gn with rfl | rfl | ⟨nl, rfl, hnl⟩
    · exact absurd rfl no
    · obtain ⟨b, hb⟩ := all_bool (K := K) "Elixir.Module.Types.Descr" "-map_check_domain_keys?/3-fun-1-" #[.map S]
        (dl.map fun e => .tuple #[e.1, e.2])
        (fun m x => Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-1-/2» (D m) (.map S) x)
        (fun m x => by simp)
        (fun x mx => by
          obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
          obtain ⟨s, hs⟩ := ops.empty (hdl e me) S
          exact ⟨s, fun m hm => by simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-1-/2», hs m hm]⟩)
      refine ⟨b, fun m hm => ?_⟩
      have all := hb m hm
      dsimp only
      cases dl with
      | nil =>
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        simp_all [fieldsTerm, Term.list]
      | cons e t =>
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        simp_all [fieldsTerm, Term.list]
    · obtain ⟨b, hb⟩ := all_bool (K := K) "Elixir.Module.Types.Descr" "-map_check_domain_keys?/3-fun-2-"
        #[.map S, fieldsTerm nl] (dl.map fun e => .tuple #[e.1, e.2])
        (fun m x => Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-2-/3» (D m) (.map S) (fieldsTerm nl) x)
        (fun m x => by simp)
        (fun x mx => by
          obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
          rcases find_entry_or_error e.1 nl with h | ⟨f, mf, h⟩
          · obtain ⟨s, hs⟩ := sub (hdl e me) ops.none
            exact ⟨s, fun m hm => by
              simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-2-/3», h, hs m hm]⟩
          · obtain ⟨s, hs⟩ := sub (hdl e me) (hnl f mf)
            exact ⟨s, fun m hm => by
              simp [Elixir.Module.Types.Descr.«-map_check_domain_keys?/3-fun-2-/3», h, hs m hm]⟩)
      refine ⟨b, fun m hm => ?_⟩
      have all : Erlang.lists.«all/2» (D m) _ (fieldsTerm dl) = _ := hb m hm
      have ne₂ := fieldsTerm_ne_atom nl
      dsimp only
      generalize fieldsTerm nl = T₂ at ne₂ all
      cases dl with
      | nil =>
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        cases T₂ <;> simp_all [fieldsTerm, Term.list]
      | cons e t =>
        rw [Elixir.Module.Types.Descr.«map_check_domain_keys?/3».eq_def]
        cases T₂ <;> simp_all [fieldsTerm, Term.list]

theorem fieldsTerm_eq_nil' {l : List (Term × Term)} : fieldsTerm l = .nil ↔ l = [] := by
  cases l <;> simp [fieldsTerm, Term.list]

/-- The walk `map_line_empty?/4` takes for a negated literal, given the answers for the remaining negations: meets of
fields when the literal is closed or the negation is open, the field walk otherwise. -/
theorem line_branch_of (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) {rest : List Term}
    (ih' : ∀ tag : Term, MapTag E tag → ∀ l : List (Term × Term), (∀ e ∈ l, FieldValue E e.2) →
      BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
        (Term.list rest) (.map S)))
    {tag ntag : Term} (gt : MapTag E tag) (gn : MapTag E ntag) {l nl : List (Term × Term)}
    (hl : ∀ e ∈ l, FieldValue E e.2) (hnl : ∀ e ∈ nl, FieldValue E e.2) :
    ∃ c : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» tag (.atom "closed"))
        (Erlang.erlang.«==/2» ntag (.atom "open")) = .ok (boolAtom c) ∧
      (c = Bool.true → tag = .atom "closed" ∨ ntag = .atom "open") ∧
      MeetAt (K + 1) (fun m => if c then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l)
        (fieldsTerm nl) tag ntag (fieldsTerm []) (Term.list rest) (.map S) else
        Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl) tag ntag
          (fieldsTerm l) (Term.list rest) (.map S)) := by
  have ops' := ops.mono (Nat.le_succ K)
  have dops' := dops.mono (Nat.le_succ K)
  have meetOk := meet_total ops' dops' S gt gn (Term.list rest) (fun l' hl' => ih' tag gt l' hl') _ l nl
    (Nat.le_refl _) hl hnl [] (by simp)
  have fieldsOk := fields_total ops' dops' S gt gn (Term.list rest) l hl (fun l' hl' => ih' tag gt l' hl') _ l nl
    (Nat.le_refl _) hl hnl
  by_cases tc : tag = .atom "closed"
  · subst tc
    exact ⟨Bool.true, by simp [Erlang.erlang.«==/2», Lynx.Except.orElse, Term.true, boolAtom], fun _ => Or.inl rfl,
      meetOk.of_eq fun m _ => by simp⟩
  by_cases no : ntag = .atom "open"
  · subst no
    exact ⟨Bool.true, by
      simp only [tag_eq_false tc]; simp [Erlang.erlang.«==/2», Lynx.Except.orElse, Term.true, boolAtom],
      fun _ => Or.inr rfl, meetOk.of_eq fun m _ => by simp⟩
  exact ⟨Bool.false, by simp [tag_eq_false tc, tag_eq_false no, Lynx.Except.orElse, boolAtom], (fun h => nomatch h),
    fieldsOk.of_eq fun m _ => by simp⟩

/-- A map line of element types minus any negated literals returns a Boolean. -/
theorem map_line_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term)) :
    ∀ negs : List Term, (∀ t ∈ negs, MapLit E t) → ∀ tag : Term, MapTag E tag →
      ∀ l : List (Term × Term), (∀ e ∈ l, FieldValue E e.2) →
      BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
        (Term.list negs) (.map S)) := by
  have ops' := ops.mono (Nat.le_succ K)
  have dops' := dops.mono (Nat.le_succ K)
  intro negs
  induction negs with
  | nil =>
    intro _ tag _ l _
    refine ⟨Bool.false, fun m _ => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
    simp [boolAtom]
  | cons N rest ih =>
    intro lits tag gt l hl
    obtain ⟨k, ntag, nl, rfl, gn, hnl⟩ := lits N List.mem_cons_self
    have ih' := ih fun t m => lits t (List.mem_cons_of_mem _ m)
    rw [list_cons]
    by_cases top : ntag = .atom "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      refine ⟨Bool.true, fun m _ => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simp [fieldsTerm, Term.list, boolAtom]
    by_cases skip : tag = .atom "open" ∧ ntag = .atom "closed"
    · obtain ⟨rfl, rfl⟩ := skip
      obtain ⟨b, hb⟩ := ih' _ gt l hl
      refine ⟨b, fun m hm => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      simpa using hb m hm
    have notTop : ¬(ntag = .atom "open" ∧ fieldsTerm nl = .nil) := fun ⟨a, b⟩ => top ⟨a, fieldsTerm_eq_nil'.mp b⟩
    clear ih lits top
    obtain ⟨bk, hk⟩ := ih' tag gt l hl
    obtain ⟨bc, hc⟩ := check_total ops dops S gt gn skip
    obtain ⟨c, hor, -, branch⟩ := line_branch_of ops dops S ih' gt gn hl hnl
    clear ih'
    have finish : ∀ (b : Bool) (m : Nat), K + 1 ≤ m →
        (bc = Bool.true → (if c then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l)
          (fieldsTerm nl) tag ntag (fieldsTerm []) (Term.list rest) (.map S) else
          Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl) tag ntag
            (fieldsTerm l) (Term.list rest) (.map S)) = .ok (boolAtom b) ∨
          ((if c then Elixir.Module.Types.Descr.«map_line_meet_empty?/7» (D m) (fieldsTerm l)
          (fieldsTerm nl) tag ntag (fieldsTerm []) (Term.list rest) (.map S) else
          Elixir.Module.Types.Descr.«map_line_fields_empty?/7» (D m) (fieldsTerm l) (fieldsTerm nl) tag ntag
            (fieldsTerm l) (Term.list rest) (.map S)) = .error (Exception.throw (.atom "closed")) ∧ b = bk)) →
        (bc = Bool.false → b = bk) →
        Elixir.Module.Types.Descr.«map_line_empty?/4» (D m) tag (fieldsTerm l)
          (Term.cons (.tuple #[.integer k, ntag, fieldsTerm nl]) (Term.list rest)) (.map S) = .ok (boolAtom b) := by
      intro b m hm hb hf
      have hk' := hk m hm
      have hc' := hc m hm
      clear hk hc
      dsimp only at hk' hc' ⊢
      have nilF : fieldsTerm ([] : List (Term × Term)) = .nil := rfl
      rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
      split
      all_goals first
        | (exfalso; simp_all; done)
        | (exfalso; rename_i h _; exact h _ _ _ _ rfl)
        | (exfalso; rename_i h; exact h _ _ _ _ rfl)
        | skip
      rename_i heq
      simp at heq
      obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := heq
      cases bc
      · simp_all [isMember, boolAtom]
      · rcases hb rfl with hb | ⟨hb, rfl⟩ <;> cases c <;> rw [hor] <;>
          simp_all [Lynx.Except.tryWith, isMember, boolAtom, Lynx.Exception.classTerm,
            Lynx.Exception.reason]
    rcases branch with ⟨b, hb⟩ | hb
    · exact ⟨if bc then b else bk, fun m hm => finish _ m hm (fun e => Or.inl (by simp [e, hb m hm]))
        (fun e => by simp [e])⟩
    · exact ⟨bk, fun m hm => finish _ m hm (fun _ => Or.inr ⟨hb m hm, rfl⟩) (fun _ => rfl)⟩

/-- `init_map_line_empty?/4` first checks whether some required field is empty. -/
theorem init_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term))
    {tag : Term} (gt : MapTag E tag) {l : List (Term × Term)} (hl : ∀ e ∈ l, FieldValue E e.2)
    {negs : List Term} (lits : ∀ t ∈ negs, MapLit E t) :
    BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D m) tag (fieldsTerm l)
      (Term.list negs) (.map S)) := by
  have each : ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]), ∃ b, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2» (D m') (.map S) x = .ok (boolAtom b) := by
    intro x mx
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
    obtain ⟨t, o, ho, ht⟩ := hl e me
    rw [ho]
    cases o
    · obtain ⟨b, hb⟩ := ops.empty ht S
      exact ⟨b, fun m' h => by
        simp only [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom]
        simpa [boolAtom] using hb m' h⟩
    · exact ⟨Bool.false, fun m' _ => by
        simp [Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2», boolAtom]⟩
  classical
  let res : Term → Bool := fun x =>
    if h : x ∈ l.map (fun e => Term.tuple #[e.1, e.2]) then Classical.choose (each x h) else Bool.false
  have hres : ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]), ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«-init_map_line_empty?/4-fun-0-/2» (D m') (.map S) x = .ok (boolAtom (res x)) := by
    intro x mx m' h
    simp only [res, dite_eq_left mx]
    exact Classical.choose_spec (each x mx) m' h
  obtain ⟨bl, hbl⟩ := map_line_total ops dops S negs lits tag gt l hl
  refine ⟨(l.map fun e => Term.tuple #[e.1, e.2]).any res || bl, fun m hm => ?_⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  have anyRun := any_list (D (n + 1)) _ _ _ res _ fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-init_map_line_empty?/4-fun-0-/1».pure]
    exact hres x mx n hn
  have line := hbl (n + 1) (by omega)
  dsimp only at line ⊢
  rw [Elixir.Module.Types.Descr.«init_map_line_empty?/4».eq_def]
  simp only [fieldsTerm] at anyRun line ⊢
  simp only [pure_bind, anyRun]
  cases (l.map fun e => Term.tuple #[e.1, e.2]).any res
  · simpa [boolAtom, Lynx.Except.orElse] using line
  · simp [boolAtom, Lynx.Except.orElse]

/-- Map BDDs of element types return a Boolean along every path. -/
theorem map_bdd_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term))
    {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → MapLit E t) → ∀ pos negs, MapPos E pos → (∀ t ∈ negs, MapLit E t) →
      BoolAt (K + 2) (fun m => Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r
        (.map S)) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLit E t) → ∀ pos negs, MapPos E pos →
    (∀ t ∈ negs, MapLit E t) →
    BoolAt (K + 2) (fun m => Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S)))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits
    obtain ⟨tag, l, rfl, gt, hl⟩ := hp
    obtain ⟨b, hb⟩ := init_total ops dops S gt hl lits
    refine ⟨b, fun m hm => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    exact hb m (by omega)
  · intro ok _ pos negs _ _
    refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    split <;> simp_all [boolAtom]
  · intro ok k x y okl okLit pos negs hp lits
    rcases map_line_ok ops S hp (okLit _ okl) with empty | ⟨pos', hp', run⟩
    · refine ⟨Bool.true, fun m hm => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [empty m hm, boolAtom]
    · obtain ⟨tag, l, rfl, gt, hl⟩ := hp'
      obtain ⟨b, hb⟩ := init_total ops dops S gt hl lits
      refine ⟨b, fun m hm => ?_⟩
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      simp [run m hm]
      exact hb m (by omega)
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits
    have okLit' : ∀ t, Above ok lit t → MapLit E t := fun t ht => okLit t ht.1
    have hl := okLit _ okl
    obtain ⟨bd, hbd⟩ := idd okLit' pos (lit :: negs) hp (fun t m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hl
      · exact lits t m)
    obtain ⟨bu, hbu⟩ := iu okLit' pos negs hp lits
    rcases map_line_ok ops S hp hl with empty | ⟨pos', hp', run⟩
    · refine ⟨bd && bu, fun m hm => ?_⟩
      have dPart := hbd m hm
      rw [list_cons] at dPart
      obtain ⟨tag, l, rfl, -⟩ := hp
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      cases bd <;> cases bu <;> simp [empty m hm, dPart, hbu m hm, Lynx.Except.andAlso, boolAtom]
    · obtain ⟨bc, hbc⟩ := ic okLit' pos' negs hp' lits
      refine ⟨bd && bc && bu, fun m hm => ?_⟩
      have dPart := hbd m hm
      rw [list_cons] at dPart
      obtain ⟨tag, l, rfl, -⟩ := hp
      obtain ⟨tag2, l2, rfl, -⟩ := hp'
      dsimp only
      rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
      cases bd <;> cases bc <;> cases bu <;>
        simp [run m hm, dPart, hbu m hm, hbc m hm, Lynx.Except.andAlso, boolAtom]

/-- Map types of element types decide their emptiness at every call depth from `K + 2`. -/
theorem map_total (ops : ElemOk E K) (dops : ElemDiff E K) (S : List (Term × Term))
    {w : Term} (field : MapField E w) :
    BoolAt (K + 2) (fun m => Elixir.Module.Types.Descr.«map_empty?/2» (D m) w (.map S)) := by
  have wl : Bdd (MapLit E) w := by
    rcases field with ⟨k, rfl⟩ | wx
    · exact Bdd.leaf_iff.mpr ⟨k, .atom "open", [], rfl, MapTag.atom_open, by simp⟩
    · exact wx.mono fun _ h => h.1
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") w) e.1) (.cons (.atom "map") w) e.1 == .eq) = Bool.true
  · refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    unfold Elixir.Module.Types.Descr.«map_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true, boolAtom]
  · have fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") w) e.1) (.cons (.atom "map") w) e.1 == .eq) = Bool.false := by
      simpa using seen
    obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "map") w) (.atom "true") (.map S) =
        .ok (.map S') := by
      simp [Erlang.maps.«put/3»]
    obtain ⟨b, hb⟩ := map_bdd_total ops dops S' wl (fun _ h => h) (.tuple #[.atom "open", .nil]) []
      ⟨.atom "open", [], rfl, MapTag.atom_open, by simp⟩ (by simp)
    refine ⟨b, fun m hm => ?_⟩
    dsimp only
    unfold Elixir.Module.Types.Descr.«map_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put]
    simpa [Term.list] using hb m hm

/-! Subtyping, field by field. -/

/-- A field of the left type that the right type covers: their difference is empty, or the right type
lacks the field and the field is empty. -/
def KeySub (d : Dispatcher) (B : List (Term × Term)) (q a : Term) : Prop :=
  (∃ b w, mapLookup B q = some b ∧ Elixir.Module.Types.Descr.«bare_difference/3» d q a b = .ok w ∧
    (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
      Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))) ∨
  (mapLookup B q = Option.none ∧ Elixir.Module.Types.Descr.«empty_key?/3» d q a (.map []) = .ok (.atom "true"))

theorem iterator_sub (d : Dispatcher) (B : List (Term × Term)) :
    ∀ es : List (Term × Term), (∀ e ∈ es, KeySub d B e.1 e.2) →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map B) (.map [])) =
        .ok (.atom "true") := by
  intro es
  induction es with
  | nil =>
    intro _
    simp [Term.list, Erlang.maps.«next/1»]
    unfold Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3»
    rfl
  | cons e rest ih =>
    intro all
    have tail := ih (fun e' m => all e' (by simp [m]))
    simp only [List.map, Term.list] at tail ⊢
    simp only [Erlang.maps.«next/1», Lynx.Except.ok_bind]
    rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
    rcases all e (by simp) with ⟨b, w, hb, run, empty⟩ | ⟨hb, empty⟩
    · simp [getMapKeys_single, hb, run]
      rcases empty with h | h | h
      · simpa [h] using tail
      · simpa [h] using tail
      · refine ⟨?_, tail⟩
        by_cases h₀ : w = .integer 0
        · simp [h₀]
        · by_cases h₁ : w = .atom "bdd_bot"
          · simp [h₁]
          · right
            simp [h₀, h₁, h]
    · simp [getMapKeys_single, hb, empty, tail]

/-- Static types are subtypes when the right type covers each field of the left type. -/
theorem subtype_keys (d : Dispatcher) (A B : List (Term × Term)) (sA : mapLookup A (.atom "dynamic") = Option.none)
    (sB : mapLookup B (.atom "dynamic") = Option.none) (keys : ∀ e ∈ mapEntries A, KeySub d B e.1 e.2) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.map A) (.map B) = .ok (.atom "true") := by
  have walk := iterator_sub d B (mapEntries A) keys
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [unfold_map, Erlang.erlang.«is_map_key/2», sA, sB, any_key, Lynx.Except.andAlso,
    Erlang.erlang.«/=/2»]
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  by_cases same : compareExact (fuel (.map B) (.map A)) (.map B) (.map A) = .eq
  · simp [Erlang.erlang.«=:=/2», same]
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, sA, Erlang.maps.«iterator/1»]
    exact walk

theorem find_entry {L : List (Term × Term)} {a : Term} {e : Term × Term}
    (hit : (mapEntries L).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) = some e) :
    compareExact (fuel a e.1) a e.1 = .eq ∧ mapLookup L a = some e.2 := by
  have qe : compareExact (fuel a e.1) a e.1 = .eq := by simpa using List.find?_some hit
  refine ⟨qe, ?_⟩
  rw [← mapLookup_mapEntries]
  simp [mapLookup, hit]

theorem find_none {L : List (Term × Term)} {a : Term}
    (hit : (mapEntries L).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) = none) : mapLookup L a = none := by
  rw [← mapLookup_mapEntries]
  simp [mapLookup, hit]

/-- The fields of an intersection of static types: the kept intersections of their common fields. -/
theorem inter_lookup (depth : Nat) (L R : List (Term × Term)) (sL : mapLookup L (.atom "dynamic") = Option.none)
    (sR : mapLookup R (.atom "dynamic") = Option.none)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) q x y = .ok w) :
    ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2» (D (depth + 1)) (.map L) (.map R) = .ok (.map I) ∧
      (∀ name, (mapLookup L (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
        (mapLookup R (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
        (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
          Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) (.atom name) x y = .ok w →
          mapLookup I (.atom name) = if kept (.atom name, w) then some w else Option.none)) ∧
      ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y w, Elixir.Module.Types.Descr.«bare_intersection/3» (D depth) q x y = .ok w → g q x y = w := by
    intro q x y w run; simp [g, run]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (depth + 1)) "Elixir.Module.Types.Descr"
    "bare_intersection" #[] L R g (by
      intro e member y hy
      obtain ⟨w, run⟩ := calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, run, value _ _ _ _ run])
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (depth + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  refine ⟨out, ?_, fun name => ?_, fun q h => ?_⟩
  · unfold Elixir.Module.Types.Descr.«bare_intersection/2»
    simp [getMapKeys_single, sL, sR]
    unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  rotate_left
  · rw [lookO] at h
    cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [hit] at h; cases h
    | some e =>
      obtain ⟨-, hI⟩ := find_entry hit
      rw [lookI] at hI
      cases hitL : (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | none => rw [hitL] at hI; cases hI
      | some f => rw [(find_entry hitL).2]; rfl
  have look : mapLookup out (.atom name) =
      match mapLookup L (.atom name), mapLookup R (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    rw [lookO, find_atom, lookI, find_atom]
    rcases hL : mapLookup L (.atom name) with _ | x <;> rcases hR : mapLookup R (.atom name) with _ | y <;>
      simp [hR]
  refine ⟨fun hL => by rw [look, hL], fun hR => by rw [look, hR]; cases mapLookup L (.atom name) <;> rfl,
    fun x y w hL hR run => by rw [look, hL, hR]; simp only [value _ _ _ _ run]⟩

/-! The meaning of fields: points hold a bit index, an atom or an arity, and a valuation of literals. -/

abbrev Point := Nat × Term × (Term → Bool)

def isListTop : Term → Bool
  | .tuple ⟨[_, .atom "term", .atom "term"]⟩ => Bool.true
  | _ => Bool.false

def isOpenTop : Term → Bool
  | .tuple ⟨[_, .atom "open", .nil]⟩ => Bool.true
  | _ => Bool.false

def bitOf : Term → Nat → Bool
  | .integer b, i => b.toNat.testBit i
  | _, _ => Bool.false

def arityOf : Term → Term → (Term → Bool) → Bool
  | .tuple ⟨[.atom "union", .map R]⟩, a, ρ => (mapLookup R a).elim Bool.false (eval ρ)
  | .tuple ⟨[.atom "negation", .map R]⟩, a, ρ => !(mapLookup R a).elim Bool.false (eval ρ)
  | _, _, _ => Bool.false

/-- List fields hold all non-empty lists, or what a BDD of other literals holds. -/
def denL (x : Term) (ρ : Term → Bool) : Bool := isListTop x || eval ρ x

theorem listTop_iff (x : Term) : isListTop x = Bool.true ↔ ∃ k, x = .tuple #[k, .atom "term", .atom "term"] := by
  unfold isListTop; split <;> simp_all

theorem listTop_bdd {x : Term} (wx : Bdd ListOk x) : isListTop x = Bool.false := by
  cases h : isListTop x
  · rfl
  · obtain ⟨k, rfl⟩ := (listTop_iff _).mp h
    exact absurd rfl (not_top_leaf wx k)

theorem denL_bdd {x : Term} (wx : Bdd ListOk x) (ρ : Term → Bool) : denL x ρ = eval ρ x := by
  simp [denL, listTop_bdd wx]

theorem denL_top (k : Int) (ρ : Term → Bool) : denL (.tuple #[.integer k, .atom "term", .atom "term"]) ρ = Bool.true := by
  simp [denL, isListTop]

theorem list_union_spec {x y : Term} (fx : ListField x) (fy : ListField y) :
    ∃ w, Elixir.Module.Types.Descr.«list_union/2» x y = .ok w ∧ ListField w ∧
      (∀ ρ, Resp ρ → denL w ρ = (denL x ρ || denL y ρ)) ∧ isListTop w = (isListTop x || isListTop y) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · refine ⟨_, by unfold Elixir.Module.Types.Descr.«list_union/2»; rfl, Or.inl ⟨k, rfl⟩, fun ρ _ => ?_, ?_⟩
    · simp [denL_top]
    · simp [isListTop]
  rcases fy with ⟨k, rfl⟩ | wy
  · have nx := not_top_leaf wx
    refine ⟨_, ?_, Or.inl ⟨k, rfl⟩, fun ρ _ => ?_, ?_⟩
    · unfold Elixir.Module.Types.Descr.«list_union/2»
      split <;> simp_all
    · simp [denL_top]
    · simp [isListTop]
  obtain ⟨w, run, keep, sem⟩ := union_ok wx wy
  have ww := keep _ wx wy
  refine ⟨w, ?_, Or.inr ww, fun ρ resp => by rw [denL_bdd ww, denL_bdd wx, denL_bdd wy, sem ρ resp], by
    rw [listTop_bdd ww, listTop_bdd wx, listTop_bdd wy]; rfl⟩
  unfold Elixir.Module.Types.Descr.«list_union/2»
  split
  · exact absurd rfl (not_top_leaf wx _)
  · exact absurd rfl (not_top_leaf wy _)
  · exact run

theorem list_bdd_ne_zero {x : Term} (wx : Bdd ListOk x) : x ≠ .integer 0 := by
  rintro rfl; simp [Bdd] at wx

theorem list_neg_spec {x : Term} (fx : ListField x) :
    ∃ w, Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x =
        .ok w ∧
      (kept (.atom "list", w) = Bool.true → ListField w ∧ isListTop w = Bool.false ∧
        ∀ ρ, Resp ρ → denL w ρ = !denL x ρ) ∧
      (kept (.atom "list", w) = Bool.false → ∀ ρ, Resp ρ → denL x ρ = Bool.true) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · refine ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«list_difference/2»; rfl, fun k => by simp [kept] at k,
      fun _ ρ _ => denL_top k ρ⟩
  obtain ⟨w, run, keep, sem, -⟩ := neg_okN wx
  have ww := keep _ wx
  refine ⟨w, by rw [list_difference_bdd _ wx, run], fun k => ⟨Or.inr ww, listTop_bdd ww, fun ρ resp => ?_⟩,
    fun k ρ resp => ?_⟩
  · rw [denL_bdd ww, denL_bdd wx, sem ρ resp]
  · rcases dropped k with h | h
    · exact absurd h (list_bdd_ne_zero ww)
    · have := sem ρ resp
      rw [h] at this
      rw [denL_bdd wx]
      cases e : eval ρ x <;> simp_all

theorem list_inter_spec {x y : Term} (fx : ListField x) (fy : ListField y) :
    ∃ w, Elixir.Module.Types.Descr.«list_intersection/2» x y = .ok w ∧
      (kept (.atom "list", w) = Bool.true → ListField w ∧ (∀ ρ, Resp ρ → denL w ρ = (denL x ρ && denL y ρ)) ∧
        isListTop w = (isListTop x && isListTop y)) ∧
      (kept (.atom "list", w) = Bool.false → (∀ ρ, Resp ρ → (denL x ρ && denL y ρ) = Bool.false) ∧
        (isListTop x && isListTop y) = Bool.false) := by
  have dropBdd : ∀ {w : Term}, Bdd ListOk w → kept (.atom "list", w) = Bool.false → ∀ ρ, eval ρ w = Bool.false := by
    intro w ww k ρ
    rcases dropped k with h | h
    · exact absurd h (list_bdd_ne_zero ww)
    · rw [h]; rfl
  rcases fx with ⟨k, rfl⟩ | wx
  · refine ⟨y, by unfold Elixir.Module.Types.Descr.«list_intersection/2»; rfl, fun _ => ⟨fy, fun ρ _ => ?_, ?_⟩,
      fun kk => ?_⟩
    · simp [denL_top]
    · simp [isListTop]
    · rcases fy with ⟨k', rfl⟩ | wy
      · simp [kept] at kk
      · exact ⟨fun ρ _ => by rw [denL_bdd wy, dropBdd wy kk]; simp, by rw [listTop_bdd wy]; simp⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · have nx := not_top_leaf wx
    refine ⟨x, ?_, fun _ => ⟨Or.inr wx, fun ρ _ => by simp [denL_top], by simp [isListTop]⟩, fun kk =>
      ⟨fun ρ _ => by rw [denL_bdd wx, dropBdd wx kk]; simp, by rw [listTop_bdd wx]; simp⟩⟩
    unfold Elixir.Module.Types.Descr.«list_intersection/2»
    split <;> simp_all
  obtain ⟨w, run, keep, sem⟩ := inter_ok wx wy
  have ww := keep _ wx wy
  refine ⟨w, ?_, fun _ => ⟨Or.inr ww, fun ρ resp => by rw [denL_bdd ww, denL_bdd wx, denL_bdd wy, sem ρ resp],
    by rw [listTop_bdd ww, listTop_bdd wx, listTop_bdd wy]; rfl⟩, fun kk => ⟨fun ρ resp => ?_,
    by rw [listTop_bdd wx]; rfl⟩⟩
  · unfold Elixir.Module.Types.Descr.«list_intersection/2»
    split
    · exact absurd rfl (not_top_leaf wx _)
    · exact absurd rfl (not_top_leaf wy _)
    · exact run
  · rw [denL_bdd wx, denL_bdd wy, ← sem ρ resp, dropBdd ww kk]

theorem list_sub_spec (d : Dispatcher) {a : Term} (fa : ListField a) (b : Option Term)
    (fb : ∀ y, b = some y → ListField y)
    (incl : ∀ ρ, Resp ρ → denL a ρ = Bool.true → b.elim Bool.false (denL · ρ) = Bool.true)
    (side : ∀ y, b = some y → isListTop y = Bool.true → isListTop a = Bool.true) :
    (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«list_difference/2» a y = .ok w ∧
      (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
        Elixir.Module.Types.Descr.«list_empty?/2» d w (.map []) = .ok (.atom "true"))) ∧
    (b = Option.none → Elixir.Module.Types.Descr.«list_empty?/2» d a (.map []) = .ok (.atom "true")) := by
  refine ⟨fun y hb => ?_, fun hb => ?_⟩
  · subst hb
    have fy := fb y rfl
    rcases fa with ⟨k, rfl⟩ | wa
    · rcases fy with ⟨k', rfl⟩ | wy
      · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«list_difference/2»; rfl, Or.inr (Or.inl rfl)⟩
      · obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        refine ⟨w, by rw [list_difference_bdd _ wy, run], Or.inr (Or.inr (list_empty_unsat d (keep _ wy)
          (fun ρ resp => ?_) []))⟩
        have := incl ρ resp (denL_top k ρ)
        simp only [Option.elim, denL_bdd wy] at this
        rw [sem ρ resp, this]; rfl
    · rcases fy with ⟨k', rfl⟩ | wy
      · have := side _ rfl (by simp [isListTop])
        rw [listTop_bdd wa] at this
        cases this
      · obtain ⟨w, run, keep, sem⟩ := diff_ok wa wy
        refine ⟨w, ?_, Or.inr (Or.inr (list_empty_unsat d (keep _ wa wy) (fun ρ resp => ?_) []))⟩
        · unfold Elixir.Module.Types.Descr.«list_difference/2»
          split
          · exact absurd rfl (not_top_leaf wa _)
          · exact absurd rfl (not_top_leaf wa _)
          · exact run
        · rw [sem ρ resp]
          cases e : eval ρ a
          · rfl
          · have := incl ρ resp (by rw [denL_bdd wa, e])
            simp only [Option.elim, denL_bdd wy] at this
            simp [this]
  · subst hb
    rcases fa with ⟨k, rfl⟩ | wa
    · have := incl _ (resp_const Bool.true) (denL_top k _)
      simp [Option.elim] at this
    · refine list_empty_unsat d wa (fun ρ resp => ?_) []
      cases e : eval ρ a
      · rfl
      · have := incl ρ resp (by rw [denL_bdd wa, e])
        simp [Option.elim] at this

/-! Map and tuple fields: all maps or tuples, or what a BDD of other literals holds. -/

def OField (ok : Term → Prop) (x : Term) : Prop := (∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd ok x

def denO (x : Term) (ρ : Term → Bool) : Bool := isOpenTop x || eval ρ x

theorem openTop_bdd {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x : Term} (wx : Bdd ok x) :
    isOpenTop x = Bool.false := by
  cases h : isOpenTop x
  · rfl
  · unfold isOpenTop at h
    split at h
    · exact absurd rfl (not_top_of_ok wx okNot _)
    · cases h

theorem denO_bdd {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x : Term} (wx : Bdd ok x) (ρ : Term → Bool) :
    denO x ρ = eval ρ x := by
  simp [denO, openTop_bdd okNot wx]

theorem denO_top (k : Term) (ρ : Term → Bool) : denO (.tuple #[k, .atom "open", .nil]) ρ = Bool.true := by
  simp [denO, isOpenTop]

theorem leaf_int {ok : Term → Prop} {k a b : Term} (w : Bdd ok (.tuple #[k, a, b])) : ∃ k' : Int, k = .integer k' := by
  rcases w.shape with e | e | ⟨k', a', b', e⟩ | ⟨h, l, c, u, d, e⟩
  · simp at e
  · simp at e
  · simp at e; exact ⟨k', e.1⟩
  · simp at e

theorem eval_exact {ok : Term → Prop} {x y : Term} (wx : Bdd ok x) {ρ : Term → Bool} (resp : Resp ρ)
    (e : compareExact (fuel y x) y x = .eq) : eval ρ y = eval ρ x :=
  (eval_congr_cmp wx resp (compare_eq_of_compareExact_eq _ _ (Lynx.Term.compareExact_eq_symm e))).symm

/-- Exactly equal open fields mean the same. -/
theorem denO_exact {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x y : Term} (fx : OField ok x)
    (fy : OField ok y) (e : compareExact (fuel y x) y x = .eq) {ρ : Term → Bool} (resp : Resp ρ) : denO y ρ = denO x ρ := by
  have top : ∀ {a b k : Term}, compareExact (fuel a (.tuple #[k, .atom "open", .nil])) a (.tuple #[k, .atom "open", .nil]) = .eq → IsTop a := fun e' => by
    obtain ⟨a, b, c, rfl, -, e₂, e₃⟩ := exact_tuple3 e'
    simp only [compareExact_eq_atom, compareExact_eq_nil] at e₂ e₃
    subst e₂ e₃
    exact ⟨a, rfl⟩
  rcases fx with ⟨k, rfl⟩ | wx
  · obtain ⟨k', rfl⟩ := top (b := y) e
    rw [denO_top, denO_top]
  rcases fy with ⟨k, rfl⟩ | wy
  · obtain ⟨k', rfl⟩ := top (b := x) (Lynx.Term.compareExact_eq_symm e)
    obtain ⟨k'', rfl⟩ := leaf_int wx
    exact absurd ⟨_, rfl⟩ (okNot _ (Bdd.leaf_iff.mp wx))
  rw [denO_bdd okNot wx, denO_bdd okNot wy]
  exact (eval_congr_cmp wx resp (compare_eq_of_compareExact_eq _ _ (Lynx.Term.compareExact_eq_symm e))).symm

theorem bdd_ne_zero {ok : Term → Prop} {x : Term} (wx : Bdd ok x) : x ≠ .integer 0 := by
  rintro rfl; simp [Bdd] at wx

theorem drop_bdd {ok : Term → Prop} {q w : Term} (ww : Bdd ok w) (k : kept (q, w) = Bool.false) (ρ : Term → Bool) :
    eval ρ w = Bool.false := by
  rcases dropped k with h | h
  · exact absurd h (bdd_ne_zero ww)
  · rw [h]; rfl

theorem open_union_spec {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) (f : Term → Term → Except Exception Term)
    (h₁ : ∀ k y, f (.tuple #[k, .atom "open", .nil]) y = .ok (.tuple #[k, .atom "open", .nil]))
    (h₂ : ∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
      f x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil]))
    (h₃ : ∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
      f x y = Elixir.Module.Types.Descr.«bdd_union/2» x y)
    {x y : Term} (fx : OField ok x) (fy : OField ok y) :
    ∃ w, f x y = .ok w ∧ OField ok w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨_, h₁ _ y, Or.inl ⟨k, rfl⟩, fun ρ _ => by simp [denO_top]⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨_, h₂ x _ (not_top_of_ok wx okNot), Or.inl ⟨k, rfl⟩, fun ρ _ => by simp [denO_top]⟩
  obtain ⟨w, run, keep, sem⟩ := union_ok wx wy
  have ww := keep _ wx wy
  exact ⟨w, by rw [h₃ x y (not_top_of_ok wx okNot) (not_top_of_ok wy okNot), run], Or.inr ww, fun ρ resp => by
    rw [denO_bdd okNot ww, denO_bdd okNot wx, denO_bdd okNot wy, sem ρ resp]⟩

theorem open_inter_spec {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) (f : Term → Term → Except Exception Term)
    (h₁ : ∀ k y, f (.tuple #[k, .atom "open", .nil]) y = .ok y)
    (h₂ : ∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) → f x (.tuple #[k, .atom "open", .nil]) = .ok x)
    (h₃ : ∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
      f x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y)
    (q : Term) {x y : Term} (fx : OField ok x) (fy : OField ok y) :
    ∃ w, f x y = .ok w ∧ (kept (q, w) = Bool.true → OField ok w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ)) ∧
      (kept (q, w) = Bool.false → ∀ ρ, Resp ρ → (denO x ρ && denO y ρ) = Bool.false) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · refine ⟨y, h₁ _ y, fun _ => ⟨fy, fun ρ _ => by simp [denO_top]⟩, fun kk ρ _ => ?_⟩
    rcases fy with ⟨k', rfl⟩ | wy
    · simp [kept] at kk
    · rw [denO_bdd okNot wy, drop_bdd wy kk]; simp
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, h₂ x _ (not_top_of_ok wx okNot), fun _ => ⟨Or.inr wx, fun ρ _ => by simp [denO_top]⟩,
      fun kk ρ _ => by rw [denO_bdd okNot wx, drop_bdd wx kk]; simp⟩
  obtain ⟨w, run, keep, sem⟩ := inter_ok wx wy
  have ww := keep _ wx wy
  refine ⟨w, by rw [h₃ x y (not_top_of_ok wx okNot) (not_top_of_ok wy okNot), run], fun _ => ⟨Or.inr ww,
    fun ρ resp => by rw [denO_bdd okNot ww, denO_bdd okNot wx, denO_bdd okNot wy, sem ρ resp]⟩, fun kk ρ resp => ?_⟩
  rw [denO_bdd okNot wx, denO_bdd okNot wy, ← sem ρ resp, drop_bdd ww kk]

theorem map_union_shape : (∀ k y, Elixir.Module.Types.Descr.«map_union/2» (.tuple #[k, .atom "open", .nil]) y =
      .ok (.tuple #[k, .atom "open", .nil])) ∧
    (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«map_union/2» x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil])) ∧
    (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«map_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y) := by
  refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => map_union_bdd⟩
  · unfold Elixir.Module.Types.Descr.«map_union/2»; rfl
  · unfold Elixir.Module.Types.Descr.«map_union/2»
    split <;> simp_all

theorem map_inter_shape : (∀ k y, Elixir.Module.Types.Descr.«map_intersection/2» (.tuple #[k, .atom "open", .nil]) y =
      .ok y) ∧
    (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«map_intersection/2» x (.tuple #[k, .atom "open", .nil]) = .ok x) ∧
    (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«map_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y) := by
  refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => map_intersection_bdd⟩
  · unfold Elixir.Module.Types.Descr.«map_intersection/2»; rfl
  · unfold Elixir.Module.Types.Descr.«map_intersection/2»
    split <;> simp_all

theorem neg_drop {a b : Bool} (sem : a = !b) (drop : a = Bool.false) : b = Bool.true := by
  subst drop; cases b <;> simp_all

theorem mapOk_not : ∀ t, MapOk E t → ¬IsTop t := fun _ h => h.2

theorem map_difference_neg {x : Term} (nt : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) (arr : Array Term)
    (hx : x = .tuple arr) {top : Int} :
    Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer top, .atom "open", .nil]) x =
      Elixir.Module.Types.Descr.«bdd_negation/1» x := by
  subst hx
  unfold Elixir.Module.Types.Descr.«map_difference/2»
  split
  · next heq => exact absurd heq (nt _)
  · next heq => rw [heq]
  · next h₁ h₂ => exact absurd rfl (h₂ _ _ rfl)

theorem map_neg_spec {x : Term} (fx : OField (MapOk E) x) :
    ∃ w, Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w ∧
      (kept (.atom "map", w) = Bool.true → OField (MapOk E) w ∧ ∀ ρ, Resp ρ → denO w ρ = !denO x ρ) ∧
      (kept (.atom "map", w) = Bool.false → ∀ ρ, Resp ρ → denO x ρ = Bool.true) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl, fun k => by simp [kept] at k,
      fun _ ρ _ => denO_top _ ρ⟩
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, fun _ ρ _ => by simp [denO, isOpenTop]⟩
    unfold Elixir.Module.Types.Descr.«map_difference/2»
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2»]
  · refine ⟨_, ?_, fun _ => ⟨Or.inl ⟨61102469, rfl⟩, fun ρ _ => by simp [denO, isOpenTop]⟩, fun k => by simp [kept] at k⟩
    unfold Elixir.Module.Types.Descr.«map_difference/2»
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2»]
  all_goals
    obtain ⟨w, run, keep, sem⟩ := neg_ok wx
    have ww := keep _ wx
    refine ⟨w, ?_, fun _ => ⟨Or.inr ww, fun ρ resp => by
      rw [denO_bdd mapOk_not ww, denO_bdd mapOk_not wx, sem ρ resp]⟩, fun kk ρ resp => ?_⟩
    · rw [map_difference_neg (not_top_of_ok wx mapOk_not) _ rfl, run]
    · rw [denO_bdd mapOk_not wx]
      exact neg_drop (sem ρ resp) (drop_bdd ww kk ρ)

theorem map_difference_bdd {a y : Term} (na : ∀ k, a ≠ .tuple #[k, .atom "open", .nil])
    (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«map_difference/2» a y = Elixir.Module.Types.Descr.«bdd_difference/2» a y := by
  unfold Elixir.Module.Types.Descr.«map_difference/2»
  split
  · exfalso; simp_all
  · exfalso; simp_all
  · rfl

theorem mapOk_lit : ∀ t, MapOk E t → MapLit E t := fun _ h => h.1

theorem map_sub_spec (ops : ElemOk E K) {m : Nat} (hm : K + 2 ≤ m) {a : Term} (fa : OField (MapOk E) a) (b : Option Term)
    (fb : ∀ y, b = some y → OField (MapOk E) y)
    (incl : ∀ ρ, Resp ρ → denO a ρ = Bool.true → b.elim Bool.false (denO · ρ) = Bool.true) :
    (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«map_difference/2» a y = .ok w ∧
      (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
        Elixir.Module.Types.Descr.«map_empty?/2» (D m) w (.map []) = .ok (.atom "true"))) ∧
    (b = Option.none → Elixir.Module.Types.Descr.«map_empty?/2» (D m) a (.map []) = .ok (.atom "true")) := by
  refine ⟨fun y hb => ?_, fun hb => ?_⟩
  · subst hb
    rcases fb y rfl with ⟨k', rfl⟩ | wy
    · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl, Or.inr (Or.inl rfl)⟩
    have ny := not_top_of_ok wy mapOk_not
    rcases fa with ⟨k, rfl⟩ | wa
    · have taut : ∀ ρ, Resp ρ → eval ρ y = Bool.true := fun ρ resp => by
        have := incl ρ resp (denO_top _ ρ)
        simpa [Option.elim, denO_bdd mapOk_not wy] using this
      rcases wy.shape with rfl | rfl | ⟨k', x', z', rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
        unfold Elixir.Module.Types.Descr.«map_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2»]
      · have := taut _ (resp_const Bool.true); simp at this
      all_goals
        obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        refine ⟨w, by rw [map_difference_neg ny _ rfl, run], Or.inr (Or.inr ?_)⟩
        exact map_empty_unsat ops (keep _ wy) mapOk_lit (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) m [] hm
    · obtain ⟨w, run, keep, sem⟩ := diff_ok wa wy
      refine ⟨w, by rw [map_difference_bdd (not_top_of_ok wa mapOk_not) ny, run], Or.inr (Or.inr ?_)⟩
      refine map_empty_unsat ops (keep _ wa wy) mapOk_lit (fun ρ resp => ?_) m [] hm
      rw [sem ρ resp]
      cases e : eval ρ a
      · rfl
      · have := incl ρ resp (by rw [denO_bdd mapOk_not wa, e])
        simp only [Option.elim, denO_bdd mapOk_not wy] at this
        simp [this]
  · subst hb
    rcases fa with ⟨k, rfl⟩ | wa
    · have := incl _ (resp_const Bool.true) (denO_top _ _)
      simp [Option.elim] at this
    · refine map_empty_unsat ops wa mapOk_lit (fun ρ resp => ?_) m [] hm
      cases e : eval ρ a
      · rfl
      · have := incl ρ resp (by rw [denO_bdd mapOk_not wa, e])
        simp [Option.elim] at this

theorem tuple_union_shape :
    (∀ k y, Elixir.Module.Types.Descr.«tuple_union/2» (.tuple #[k, .atom "open", .nil]) y =
      .ok (.tuple #[k, .atom "open", .nil])) ∧
    (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«tuple_union/2» x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil])) ∧
    (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«tuple_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y) := by
  refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => tuple_union_bdd⟩
  · unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl
  · unfold Elixir.Module.Types.Descr.«tuple_union/2»
    split <;> simp_all

theorem tuple_inter_shape :
    (∀ k y, Elixir.Module.Types.Descr.«tuple_intersection/2» (.tuple #[k, .atom "open", .nil]) y = .ok y) ∧
    (∀ x k, (∀ k', x ≠ .tuple #[k', .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«tuple_intersection/2» x (.tuple #[k, .atom "open", .nil]) = .ok x) ∧
    (∀ x y, (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) → (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) →
      Elixir.Module.Types.Descr.«tuple_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y) := by
  refine ⟨fun k y => ?_, fun x k nx => ?_, fun x y => tuple_intersection_bdd⟩
  · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»; rfl
  · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
    split <;> simp_all

theorem tupleOk_not : ∀ t, TupleOk E t → ¬IsTop t := fun _ h => h.2

/-- The difference of the top tuple and `{}`: tuples with at least one element. -/
theorem tuple_minus_empty (k : Int) : ∃ H : Int, Elixir.Module.Types.Descr.«tuple_difference/2»
    (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "closed", .nil]) =
      .ok (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
  refine ⟨(1 <<< 27) + hash, ?_⟩
  unfold Elixir.Module.Types.Descr.«tuple_difference/2»
  simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
    Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»,
    Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
  rfl

theorem tuple_difference_neg {x : Term} (nt : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ne : ∀ k, x ≠ .tuple #[k, .atom "closed", .nil]) (arr : Array Term) (hx : x = .tuple arr) {top : Int} :
    Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer top, .atom "open", .nil]) x =
      Elixir.Module.Types.Descr.«bdd_negation/1» x := by
  subst hx
  unfold Elixir.Module.Types.Descr.«tuple_difference/2»
  split
  · exfalso; simp_all
  · exfalso; simp_all
  · next heq => rw [heq]
  · next h₁ h₂ h₃ => exact absurd rfl (h₃ _ _ rfl)

theorem tuple_difference_bdd {a y : Term} (na : ∀ k, a ≠ .tuple #[k, .atom "open", .nil])
    (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (special : ¬((∃ k e, a = .tuple #[k, .atom "open", e]) ∧ ∃ k, y = .tuple #[k, .atom "closed", .nil])) :
    Elixir.Module.Types.Descr.«tuple_difference/2» a y = Elixir.Module.Types.Descr.«bdd_difference/2» a y := by
  unfold Elixir.Module.Types.Descr.«tuple_difference/2»
  split
  · exfalso; simp_all
  · next heq₁ heq₂ => exact absurd ⟨⟨_, _, rfl⟩, ⟨_, rfl⟩⟩ special
  · exfalso; simp_all
  · rfl

theorem tuple_neg_spec (hterm : E (.atom "term")) {x : Term} (fx : OField (TupleOk E) x) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (TupleOk E) w ∧ ∀ ρ, Resp ρ → Real ρ → denO w ρ = !denO x ρ) ∧
      (kept (.atom "tuple", w) = Bool.false → ∀ ρ, Resp ρ → Real ρ → denO x ρ = Bool.true) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, fun k => by simp [kept] at k,
      fun _ ρ _ _ => denO_top _ ρ⟩
  have nt := not_top_of_ok wx tupleOk_not
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, fun _ ρ _ _ => by simp [denO, isOpenTop]⟩
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2»]
  · refine ⟨_, ?_, fun _ => ⟨Or.inl ⟨61102469, rfl⟩, fun ρ _ _ => by simp [denO, isOpenTop]⟩,
      fun k => by simp [kept] at k⟩
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2»]
  · by_cases special : a = .atom "closed" ∧ b = .nil
    · obtain ⟨rfl, rfl⟩ := special
      obtain ⟨H, run⟩ := tuple_minus_empty k
      have lit : TupleOk E (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) :=
        ⟨⟨H, "open", [.atom "term"], rfl, Or.inl rfl, fun e me => by rw [List.mem_singleton.mp me]; exact hterm⟩,
          fun ⟨_, e⟩ => by simp [Term.list] at e⟩
      refine ⟨_, run, fun _ => ⟨Or.inr (Bdd.leaf_iff.mpr lit), fun ρ _ ⟨e, c⟩ => ?_⟩, fun k => by simp [kept] at k⟩
      simp only [denO, isOpenTop, Term.list, eval_leaf, Bool.false_or]
      rw [c.2.1 _ ⟨_, rfl⟩, c.1 _ ⟨_, rfl⟩]
    · have ne : ∀ k', Term.tuple #[.integer k, a, b] ≠ .tuple #[k', .atom "closed", .nil] := by
        intro k' e; simp at e; exact special ⟨e.2.1, e.2.2⟩
      obtain ⟨w, run, keep, sem⟩ := neg_ok wx
      have ww := keep _ wx
      exact ⟨w, by rw [tuple_difference_neg nt ne _ rfl, run], fun _ => ⟨Or.inr ww, fun ρ resp _ => by
        rw [denO_bdd tupleOk_not ww, denO_bdd tupleOk_not wx, sem ρ resp]⟩, fun kk ρ resp _ => by
        rw [denO_bdd tupleOk_not wx]; exact neg_drop (sem ρ resp) (drop_bdd ww kk ρ)⟩
  · obtain ⟨w, run, keep, sem⟩ := neg_ok wx
    have ww := keep _ wx
    exact ⟨w, by rw [tuple_difference_neg nt (fun _ e => by simp at e) _ rfl, run], fun _ => ⟨Or.inr ww,
      fun ρ resp _ => by rw [denO_bdd tupleOk_not ww, denO_bdd tupleOk_not wx, sem ρ resp]⟩, fun kk ρ resp _ => by
      rw [denO_bdd tupleOk_not wx]; exact neg_drop (sem ρ resp) (drop_bdd ww kk ρ)⟩

theorem real_realize (e : Bool) : Real (realize e) := ⟨e, realize_consistent e⟩

theorem tuple_sub_spec (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K + 1 ≤ m) {a : Term} (fa : OField (TupleOk E) a)
    (b : Option Term)
    (fb : ∀ y, b = some y → OField (TupleOk E) y)
    (incl : ∀ ρ, Resp ρ → Real ρ → denO a ρ = Bool.true → b.elim Bool.false (denO · ρ) = Bool.true) :
    (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» a y = .ok w ∧
      (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
        Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) w (.map []) = .ok (.atom "true"))) ∧
    (b = Option.none → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) a (.map []) = .ok (.atom "true")) := by
  have realF := realize_resp Bool.false
  have consF := realize_consistent Bool.false
  refine ⟨fun y hb => ?_, fun hb => ?_⟩
  · subst hb
    rcases fb y rfl with ⟨k', rfl⟩ | wy
    · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, Or.inr (Or.inl rfl)⟩
    have ny := not_top_of_ok wy tupleOk_not
    have yE : ∀ k, y = .tuple #[k, .atom "closed", .nil] → denO a (realize Bool.false) = Bool.false := by
      intro k e
      cases ha : denO a (realize Bool.false)
      · rfl
      · have := incl _ realF (real_realize _) ha
        simp only [Option.elim, e, denO, isOpenTop, eval_leaf] at this
        rw [consF.1 _ ⟨_, rfl⟩] at this
        cases this
    rcases fa with ⟨k, rfl⟩ | wa
    · have taut : ∀ ρ, Resp ρ → Real ρ → eval ρ y = Bool.true := fun ρ resp real => by
        have := incl ρ resp real (denO_top _ ρ)
        simpa [Option.elim, denO_bdd tupleOk_not wy] using this
      rcases wy.shape with rfl | rfl | ⟨k', x', z', rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2»]
      · have := taut _ realF (real_realize _); simp at this
      · by_cases special : x' = .atom "closed" ∧ z' = .nil
        · obtain ⟨rfl, rfl⟩ := special
          have := yE _ rfl
          simp [denO, isOpenTop] at this
        have ne : ∀ k'', Term.tuple #[.integer k', x', z'] ≠ .tuple #[k'', .atom "closed", .nil] := by
          intro k'' e; simp at e; exact special ⟨e.2.1, e.2.2⟩
        obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        refine ⟨w, ?_, Or.inr (Or.inr (tuple_empty_real ops dops hm (fun _ h => h) (keep _ wy) fun ρ resp real => ?_))⟩
        · rw [tuple_difference_neg ny ne _ rfl, run]
        · rw [sem ρ resp, taut ρ resp real]; rfl
      · obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        refine ⟨w, ?_, Or.inr (Or.inr (tuple_empty_real ops dops hm (fun _ h => h) (keep _ wy) fun ρ resp real => ?_))⟩
        · rw [tuple_difference_neg ny (fun _ e => by simp at e) _ rfl, run]
        · rw [sem ρ resp, taut ρ resp real]; rfl
    · have na := not_top_of_ok wa tupleOk_not
      by_cases special : (∃ k e, a = .tuple #[k, .atom "open", e]) ∧ ∃ k, y = .tuple #[k, .atom "closed", .nil]
      · obtain ⟨⟨k, e, rfl⟩, ⟨k', hy⟩⟩ := special
        have := yE k' hy
        obtain ⟨⟨k₀, tag, l, eq, -, -⟩, notTop⟩ : TupleOk E (.tuple #[k, .atom "open", e]) := by
          rcases wa.shape with h | h | ⟨k₁, x₁, y₁, h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact Bdd.leaf_iff.mp wa
        simp at eq
        obtain ⟨rfl, -, rfl⟩ := eq
        have notE : ¬IsE' (.tuple #[.integer k₀, .atom "open", Term.list l]) := fun ⟨_, e⟩ => by simp at e
        simp only [denO, eval_leaf] at this
        have r : realize Bool.false (.tuple #[.integer k₀, .atom "open", Term.list l]) = Bool.true := by
          by_cases h : IsH' (.tuple #[.integer k₀, .atom "open", Term.list l]) <;> simp [realize, notE, h]
        simp [r] at this
      obtain ⟨w, run, keep, sem⟩ := diff_ok wa wy
      refine ⟨w, by rw [tuple_difference_bdd na ny special, run],
        Or.inr (Or.inr (tuple_empty_real ops dops hm (fun _ h => h) (keep _ wa wy) fun ρ resp real => ?_))⟩
      rw [sem ρ resp]
      cases e : eval ρ a
      · rfl
      · have := incl ρ resp real (by rw [denO_bdd tupleOk_not wa, e])
        simp only [Option.elim, denO_bdd tupleOk_not wy] at this
        simp [this]
  · subst hb
    rcases fa with ⟨k, rfl⟩ | wa
    · have := incl _ realF (real_realize _) (denO_top _ _)
      simp [Option.elim] at this
    · refine tuple_empty_real ops dops hm (fun _ h => h) wa fun ρ resp real => ?_
      cases e : eval ρ a
      · rfl
      · have := incl ρ resp real (by rw [denO_bdd tupleOk_not wa, e])
        simp [Option.elim] at this

/-! Bitmap fields. -/

def BitField (x : Term) : Prop := ∃ b : Nat, x = .integer b ∧ 1 ≤ b ∧ b ≤ 255

theorem bitOf_nat (b i : Nat) : bitOf (.integer b) i = b.testBit i := by simp [bitOf]

theorem small_bit {b i : Nat} (le : b ≤ 255) (h : b.testBit i = Bool.true) : i < 8 := by
  refine Classical.byContradiction fun hi => ?_
  have : b < 2 ^ i := Nat.lt_of_lt_of_le (by omega : b < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow this] at h
  cases h

theorem bit_union (d : Dispatcher) {x y : Term} (fx : BitField x) (fy : BitField y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "bitmap") x y = .ok w ∧ BitField w ∧
      ∀ i, bitOf w i = (bitOf x i || bitOf y i) := by
  obtain ⟨a, rfl, a1, a2⟩ := fx
  obtain ⟨b, rfl, b1, b2⟩ := fy
  refine ⟨.integer ↑(a ||| b), ?_, ⟨a ||| b, rfl, Nat.le_trans a1 Nat.left_le_or, ?_⟩, fun i => by
    simp [bitOf_nat, Nat.testBit_or]⟩
  · simp [Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
  · have := Nat.or_lt_two_pow (n := 8) (by omega : a < 2 ^ 8) (by omega : b < 2 ^ 8)
    omega

theorem bit_inter (d : Dispatcher) {x y : Term} (fx : BitField x) (fy : BitField y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "bitmap") x y = .ok w ∧
      (kept (.atom "bitmap", w) = Bool.true → BitField w ∧ ∀ i, bitOf w i = (bitOf x i && bitOf y i)) ∧
      (kept (.atom "bitmap", w) = Bool.false → ∀ i, (bitOf x i && bitOf y i) = Bool.false) := by
  obtain ⟨a, rfl, a1, a2⟩ := fx
  obtain ⟨b, rfl, b1, b2⟩ := fy
  refine ⟨.integer ↑(a &&& b), by simp [Elixir.Module.Types.Descr.«bare_intersection/3», bandI], fun k => ⟨?_, fun i => by
    simp [bitOf_nat, Nat.testBit_and]⟩, fun k i => ?_⟩
  · have le : a &&& b ≤ a := Nat.and_le_left
    refine ⟨a &&& b, rfl, ?_, by omega⟩
    by_cases zero : a &&& b = 0
    · simp [kept, zero] at k
    · omega
  · have zero : a &&& b = 0 := by
      rcases dropped k with h | h <;> simp at h
      omega
    have := congrArg (·.testBit i) zero
    simp only [Nat.testBit_and, Nat.zero_testBit] at this
    simp [bitOf_nat, this]

theorem bit_neg (d : Dispatcher) {x : Term} (fx : BitField x) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "bitmap") (.integer 255) x = .ok w ∧
      (kept (.atom "bitmap", w) = Bool.true → BitField w ∧ ∀ i, i < 8 → bitOf w i = !bitOf x i) ∧
      (kept (.atom "bitmap", w) = Bool.false → ∀ i, i < 8 → bitOf x i = Bool.true) := by
  obtain ⟨b, rfl, b1, b2⟩ := fx
  have band := band_255 b2
  have bit255 : ∀ i, i < 8 → (255 : Nat).testBit i = Bool.true := by decide
  refine ⟨.integer ↑(255 - b), ?_, fun k => ⟨⟨255 - b, rfl, ?_, by omega⟩, fun i lt => ?_⟩, fun k i lt => ?_⟩
  · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]
    omega
  · by_cases zero : 255 - b = 0
    · simp [kept, zero] at k
    · omega
  · have := testBit_sub_and 255 b i
    rw [band] at this
    simp [bitOf_nat, this, bit255 i lt]
  · have zero : 255 - b = 0 := by
      rcases dropped k with h | h <;> simp at h
      omega
    have : b = 255 := by omega
    subst this
    simpa [bitOf] using bit255 i lt

theorem bit_sub (d : Dispatcher) {a : Term} (fa : BitField a) (b : Option Term) (fb : ∀ y, b = some y → BitField y)
    (incl : ∀ i, i < 8 → bitOf a i = Bool.true → b.elim Bool.false (bitOf · i) = Bool.true) :
    (∀ y, b = some y → Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "bitmap") a y = .ok (.integer 0)) ∧
    b ≠ Option.none := by
  obtain ⟨x, rfl, x1, x2⟩ := fa
  refine ⟨fun y hb => ?_, fun hb => ?_⟩
  · subst hb
    obtain ⟨z, rfl, -, z2⟩ := fb _ rfl
    have sub : x &&& z = x := Nat.eq_of_testBit_eq fun i => by
      simp only [Nat.testBit_and]
      cases h : x.testBit i
      · rfl
      · have := incl i (small_bit x2 h) (by simp [bitOf_nat, h])
        simp [Option.elim, bitOf_nat] at this
        simp [this]
    simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», sub]
  · subst hb
    obtain ⟨i, hi⟩ : ∃ i, x.testBit i = Bool.true := Nat.exists_testBit_of_ne_zero (by omega)
    have := incl i (small_bit x2 hi) (by simp [bitOf_nat, hi])
    simp [Option.elim] at this

/-! Atom fields. -/

def AtomF (x : Term) : Prop := AtomField x ∧ ∃ q, amemV (some x) q = Bool.true

theorem atom_union_spec (d : Dispatcher) {x y : Term} (fx : AtomF x) (fy : AtomF y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "atom") x y = .ok w ∧ AtomF w ∧
      ∀ q, amemV (some w) q = (amemV (some x) q || amemV (some y) q) := by
  obtain ⟨⟨p₁, S₁, rfl, set₁⟩, q, hq⟩ := fx
  obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fy
  obtain ⟨p, E, run, setE, mem⟩ := atom_union p₁ S₁ p₂ S₂ set₁ set₂
  have sem : ∀ q, amemV (some (.tuple #[.atom (if p then "union" else "negation"), .map E])) q =
      (amemV (some (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])) q ||
        amemV (some (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂])) q) := by
    intro q; rw [amemV_field, amemV_field, amemV_field, mem q]
  exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], ⟨⟨p, E, rfl, setE⟩, q, by rw [sem q, hq]; rfl⟩, sem⟩

theorem atom_inter_spec (d : Dispatcher) {x y : Term} (fx : AtomF x) (fy : AtomF y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "atom") x y = .ok w ∧
      (kept (.atom "atom", w) = Bool.true → AtomF w ∧
        ∀ q, amemV (some w) q = (amemV (some x) q && amemV (some y) q)) ∧
      (kept (.atom "atom", w) = Bool.false → ∀ q, (amemV (some x) q && amemV (some y) q) = Bool.false) := by
  obtain ⟨⟨p₁, S₁, rfl, set₁⟩, -⟩ := fx
  obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fy
  rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, run, setE, -, ne, mem⟩ | ⟨run, mem⟩
  · refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun _ => ⟨⟨⟨p, E, rfl, setE⟩,
      atom_nonempty p E ne⟩, fun q => ?_⟩, fun k => by simp [kept] at k⟩
    rw [amemV_field, amemV_field, amemV_field, mem q]
  · refine ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun k => by simp [kept] at k,
      fun _ q => ?_⟩
    rw [amemV_field, amemV_field]
    exact mem q

theorem atom_neg_spec (d : Dispatcher) {x : Term} (fx : AtomF x) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "atom") (.tuple #[.atom "negation", .map []]) x =
        .ok w ∧
      (kept (.atom "atom", w) = Bool.true → AtomF w ∧ ∀ q, amemV (some w) q = !amemV (some x) q) ∧
      (kept (.atom "atom", w) = Bool.false → ∀ q, amemV (some x) q = Bool.true) := by
  obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fx
  have top : ∀ q, amemV (some (.tuple #[.atom "negation", .map []])) q = Bool.true := by
    intro q; simp [amemV, mapLookup]
  rcases atom_difference Bool.false [] p₂ S₂ no_atoms set₂ with ⟨p, E, run, setE, -, ne, mem⟩ | ⟨run, mem⟩
  · refine ⟨_, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, fun _ => ⟨⟨⟨p, E, rfl, setE⟩,
      atom_nonempty p E ne⟩, fun q => ?_⟩, fun k => by simp [kept] at k⟩
    have := mem q
    rw [amemV_field, amemV_field, this]
    simp [mapLookup]
  · refine ⟨_, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, fun k => by simp [kept] at k,
      fun _ q => ?_⟩
    have := mem q
    rw [amemV_field]
    have empty : (mapLookup ([] : List (Term × Term)) q).isSome = Bool.false := by simp [mapLookup]
    rw [empty] at this
    cases p₂ <;> cases h : (mapLookup S₂ q).isSome <;> simp_all

theorem atom_sub_spec (d : Dispatcher) {a : Term} (fa : AtomF a) (b : Option Term) (fb : ∀ y, b = some y → AtomF y)
    (incl : ∀ q, amemV (some a) q = Bool.true → b.elim Bool.false (fun y => amemV (some y) q) = Bool.true) :
    (∀ y, b = some y → Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "atom") a y = .ok (.integer 0)) ∧
    b ≠ Option.none := by
  obtain ⟨⟨p₁, S₁, rfl, set₁⟩, q₀, hq₀⟩ := fa
  refine ⟨fun y hb => ?_, fun hb => ?_⟩
  · subst hb
    obtain ⟨⟨p₂, S₂, rfl, set₂⟩, -⟩ := fb _ rfl
    have none : ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome)) = Bool.false := by
      intro q
      have := incl q
      rw [amemV_field] at this
      simp only [Option.elim, amemV_field] at this
      cases h₁ : (p₁ == (mapLookup S₁ q).isSome) <;> simp_all
    rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, run, -, -, ne, mem⟩ | ⟨run, -⟩
    · exfalso
      obtain ⟨q, hq⟩ := atom_nonempty p E ne
      rw [amemV_field, mem q, none q] at hq
      cases hq
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», run]
  · subst hb
    have := incl q₀ hq₀
    simp [Option.elim] at this

/-! Function fields: per arity, the propositional semantics of its BDD, negated for negations. -/

theorem repr_diff_step (g : Term → Term → Term → Term) (acc : List (Term × Term)) (key v₂ : Term)
    (calls : ∀ v₁, mapLookup acc key = some v₁ →
      Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ = .ok (g key v₁ v₂)) :
    Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3» key v₂ (.map acc) =
      .ok (.map (differenceStep g acc (key, v₂))) := by
  unfold Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3»
  cases found : mapLookup acc key with
  | none => simp [getMapKeys_single, found, differenceStep]
  | some v₁ =>
    simp only [getMapKeys_single, found, Option.toList_some, calls v₁ found, Lynx.Except.ok_bind, member_dropped key,
      differenceStep]
    obtain ⟨e, member, same⟩ := (mapLookup_isSome acc key).mp (by simp [found])
    by_cases keep : kept (key, g key v₁ v₂) <;> simp [keep, Erlang.erlang.«is_map/1», Erlang.maps.«update/3»,
      Erlang.maps.«remove/2»]
    exact ⟨e.1, ⟨e.2, member⟩, same⟩

theorem repr_diff_fold (n : Nat) (g : Term → Term → Term → Term) (es acc : List (Term × Term))
    (distinct : es.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq))
    (calls : ∀ e ∈ es, ∀ v₁, mapLookup acc e.1 = some v₁ →
      Elixir.Module.Types.Descr.«bdd_difference/2» v₁ e.2 = .ok (g e.1 v₁ e.2)) :
    ∃ M, es.foldlM (fun acc entry =>
        (Dispatch.dispatch (D n) (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
          #[entry.1, entry.2, acc] : Except Exception Term)) (.map acc) = .ok (.map M) ∧
      (∀ q, mapLookup M q =
        match es.find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => (mapLookup acc e.1).bind fun v₁ =>
            if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none
        | none => mapLookup acc q) ∧ M = es.foldl (differenceStep g) acc := by
  induction es generalizing acc with
  | nil => exact ⟨acc, rfl, fun q => rfl, rfl⟩
  | cons e rest ih =>
    have apart := List.pairwise_cons.mp distinct
    have step : (Dispatch.dispatch (D n) (.function "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
        #[e.1, e.2, .map acc] : Except Exception Term) = .ok (.map (differenceStep g acc e)) := by
      rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure,
        repr_diff_step g acc e.1 e.2 (calls e (List.mem_cons_self ..))]
    obtain ⟨M, run, look, explicit⟩ := ih (differenceStep g acc e) apart.2 (by
      intro e' member v₁ found
      rw [step_other g acc e e'.1 (fun same => apart.1 e' member (Lynx.Term.compareExact_eq_symm same))] at found
      exact calls e' (List.mem_cons_of_mem _ member) v₁ found)
    refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_,
      by rw [explicit]; rfl⟩
    rw [look q]
    by_cases same : compareExact (fuel q e.1) q e.1 = .eq
    · have absent : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) = none := by
        rw [List.find?_eq_none]
        intro p member hit
        exact apart.1 p member (Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_symm same) (of_decide_eq_true hit))
      simp only [absent, List.find?_cons, same, decide_true]
      exact step_same g acc e q same
    · simp only [List.find?_cons, same, decide_false]
      cases hit : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) with
      | none => exact step_other g acc e q same
      | some e' =>
        have qe' : compareExact (fuel q e'.1) q e'.1 = .eq := by simpa using List.find?_some hit
        have other : compareExact (fuel e'.1 e.1) e'.1 e.1 ≠ .eq := fun same' => same (Lynx.Term.compareExact_eq_trans qe' same')
        simp only
        rw [step_other g acc e e'.1 other]

def evalR (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) : Bool := (mapLookup R a).elim Bool.false (eval ρ)

/-- Maps whose values are BDDs, with literals of each key satisfying `P`. -/
def AllBddP (P : Term → Term → Prop) (R : List (Term × Term)) : Prop :=
  ∀ q v, mapLookup R q = some v → Bdd (P q) v

abbrev AllBdd (R : List (Term × Term)) : Prop := AllBddP (fun _ _ => True) R

theorem repr_union_sem (n : Nat) {P : Term → Term → Prop} {R₁ R₂ : List (Term × Term)} (b₁ : AllBddP P R₁) (b₂ : AllBddP P R₂) :
    ∃ M, Elixir.Module.Types.Descr.«fun_repr_union/2» (D (n + 1)) (.map R₁) (.map R₂) = .ok (.map M) ∧ AllBddP P M ∧
      (∀ a ρ, Resp ρ → evalR M a ρ = (evalR R₁ a ρ || evalR R₂ a ρ)) ∧
      (∀ a, (mapLookup R₁ a).isSome → (mapLookup M a).isSome) ∧
      ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome ∨ (mapLookup R₂ a).isSome := by
  let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bdd_union/2» v₁ v₂ with | .ok w => w | .error _ => .nil
  have gspec : ∀ k v₁ v₂, Bdd (P k) v₁ → Bdd (P k) v₂ →
      Elixir.Module.Types.Descr.«bdd_union/2» v₁ v₂ = .ok (g k v₁ v₂) ∧ Bdd (P k) (g k v₁ v₂) ∧
        ∀ ρ, Resp ρ → eval ρ (g k v₁ v₂) = (eval ρ v₁ || eval ρ v₂) := by
    intro k v₁ v₂ w₁ w₂
    obtain ⟨r, run, keep, sem⟩ := union_ok w₁ w₂
    have : g k v₁ v₂ = r := by simp [g, run]
    rw [this]
    exact ⟨run, keep _ w₁ w₂, sem⟩
  obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
    "-fun_repr_union/2-fun-0-" #[] R₁ R₂ g (by
      intro e me v hv
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_union/2-fun-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-fun_repr_union/2-fun-0-/3»]
      exact (gspec e.1 _ _ (b₁ _ _ hv) (b₂ _ _ (mapLookup_of_mem_mapEntries me))).1)
  have shape : ∀ a, (∃ v₁ v₂, mapLookup R₁ a = some v₁ ∧ mapLookup R₂ a = some v₂ ∧
      mapLookup out a = some (g a v₁ v₂)) ∨ (mapLookup R₂ a = none ∧ mapLookup out a = mapLookup R₁ a) ∨
      (mapLookup R₁ a = none ∧ mapLookup out a = mapLookup R₂ a) := by
    intro a
    rw [look a]
    cases hit : (mapEntries R₂).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) with
    | none => exact Or.inr (Or.inl ⟨find_none hit, rfl⟩)
    | some e =>
      obtain ⟨qe, h₂⟩ := find_entry hit
      cases h₁ : mapLookup R₁ e.1 with
      | none =>
        refine Or.inr (Or.inr ⟨by rw [mapLookup_congr qe]; exact h₁, by simp [h₁, h₂]⟩)
      | some v₁ =>
        exact Or.inl ⟨v₁, e.2, by rw [mapLookup_congr qe]; exact h₁, h₂, by simp [h₁]; rfl⟩
  refine ⟨out, by simp [Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», run],
    fun q v h => ?_, fun a ρ resp => ?_, fun a h => ?_, fun a h => ?_⟩
  rotate_left 2
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨h₁, h₃⟩ <;> rw [h₃]
    · rfl
    · exact h
    · rw [h₁] at h; cases h
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
    · simp [h₁]
    · exact Or.inl h
    · exact Or.inr h
  · rcases shape q with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
    · cases h; exact (gspec q _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1
    · exact b₁ _ _ h
    · exact b₂ _ _ h
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨h₂, h₃⟩ | ⟨h₁, h₃⟩ <;> simp only [evalR, h₃]
    · simp [h₁, h₂, (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.2 ρ resp]
    · simp [h₂]
    · simp [h₁]

theorem repr_inter_sem (n : Nat) {P : Term → Term → Prop} {R₁ R₂ : List (Term × Term)} (b₁ : AllBddP P R₁) (b₂ : AllBddP P R₂) :
    ∃ M, Elixir.Module.Types.Descr.«fun_repr_intersection/2» (D (n + 1)) (.map R₁) (.map R₂) = .ok (.map M) ∧
      AllBddP P M ∧ (∀ a ρ, Resp ρ → evalR M a ρ = (evalR R₁ a ρ && evalR R₂ a ρ)) ∧
      ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome := by
  let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bdd_intersection/2» v₁ v₂ with | .ok w => w | .error _ => .nil
  have gspec : ∀ k v₁ v₂, Bdd (P k) v₁ → Bdd (P k) v₂ →
      Elixir.Module.Types.Descr.«bdd_intersection/2» v₁ v₂ = .ok (g k v₁ v₂) ∧ Bdd (P k) (g k v₁ v₂) ∧
        ∀ ρ, Resp ρ → eval ρ (g k v₁ v₂) = (eval ρ v₁ && eval ρ v₂) := by
    intro k v₁ v₂ w₁ w₂
    obtain ⟨r, run, keep, sem⟩ := inter_ok w₁ w₂
    have : g k v₁ v₂ = r := by simp [g, run]
    rw [this]
    exact ⟨run, keep _ w₁ w₂, sem⟩
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
    "-fun_repr_intersection/2-fun-0-" #[] R₁ R₂ g (by
      intro e me v hv
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_intersection/2-fun-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-fun_repr_intersection/2-fun-0-/3»]
      exact (gspec e.1 _ _ (b₁ _ _ (mapLookup_of_mem_mapEntries me)) (b₂ _ _ hv)).1)
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  have shape : ∀ a, (∃ v₁ v₂, mapLookup R₁ a = some v₁ ∧ mapLookup R₂ a = some v₂ ∧
      mapLookup out a = if kept (a, g a v₁ v₂) then some (g a v₁ v₂) else none) ∨
      ((mapLookup R₁ a = none ∨ mapLookup R₂ a = none) ∧ mapLookup out a = none) := by
    intro a
    rw [lookO a]
    cases hitI : (mapEntries I).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) with
    | none =>
      have hI := find_none hitI
      rw [lookI a] at hI
      refine Or.inr ⟨?_, rfl⟩
      cases hit : (mapEntries R₁).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) with
      | none => exact Or.inl (find_none hit)
      | some e =>
        rw [hit] at hI
        obtain ⟨qe, -⟩ := find_entry hit
        right
        rw [mapLookup_congr qe]
        simpa using hI
    | some eI =>
      obtain ⟨qI, hI⟩ := find_entry hitI
      rw [lookI a] at hI
      cases hit : (mapEntries R₁).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) with
      | none => rw [hit] at hI; cases hI
      | some e =>
        rw [hit] at hI
        obtain ⟨qe, h₁⟩ := find_entry hit
        obtain ⟨v₂, h₂, value⟩ := Option.map_eq_some_iff.mp hI
        refine Or.inl ⟨e.2, v₂, h₁, by rw [mapLookup_congr qe]; exact h₂, ?_⟩
        have : kept eI = kept (a, g a e.2 v₂) := by unfold kept; rw [← value]
        show (if kept eI = Bool.true then some eI.2 else none) = _
        rw [this, ← value]
  refine ⟨out, ?_, fun q v h => ?_, fun a ρ resp => ?_, fun a h => ?_⟩
  rotate_left 3
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
    · simp [h₁]
    · cases h
  · simp [Elixir.Module.Types.Descr.«fun_repr_intersection/2»]
    unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  · rcases shape q with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
    · split at h
      · cases h; exact (gspec q _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1
      · cases h
    · cases h
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨h₁₂, h₃⟩
    · have sem := (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.2 ρ resp
      by_cases k : kept (a, g a v₁ v₂) = Bool.true
      · simp [evalR, h₁, h₂, h₃, k, sem]
      · have := drop_bdd (ok := P a) (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1 (by simpa using k) ρ
        simp [evalR, h₁, h₂, h₃, k, ← sem, this]
    · rcases h₁₂ with h | h <;> simp [evalR, h, h₃]

theorem repr_diff_sem (n : Nat) {P : Term → Term → Prop} {R₁ R₂ : List (Term × Term)} (b₁ : AllBddP P R₁) (b₂ : AllBddP P R₂) :
    ∃ M, Elixir.Module.Types.Descr.«fun_repr_difference/2» (D n) (.map R₁) (.map R₂) = .ok (.map M) ∧
      AllBddP P M ∧ (∀ a ρ, Resp ρ → evalR M a ρ = (evalR R₁ a ρ && !evalR R₂ a ρ)) ∧
      ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome := by
  let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ with | .ok w => w | .error _ => .nil
  have gspec : ∀ k v₁ v₂, Bdd (P k) v₁ → Bdd (P k) v₂ →
      Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ = .ok (g k v₁ v₂) ∧ Bdd (P k) (g k v₁ v₂) ∧
        ∀ ρ, Resp ρ → eval ρ (g k v₁ v₂) = (eval ρ v₁ && !eval ρ v₂) := by
    intro k v₁ v₂ w₁ w₂
    obtain ⟨r, run, keep, sem⟩ := diff_ok w₁ w₂
    have : g k v₁ v₂ = r := by simp [g, run]
    rw [this]
    exact ⟨run, keep _ w₁ w₂, sem⟩
  obtain ⟨M, run, look, -⟩ := repr_diff_fold n g (mapEntries R₂) R₁ (mapEntries_distinct R₂) (by
    intro e me v hv
    exact (gspec e.1 _ _ (b₁ _ _ hv) (b₂ _ _ (mapLookup_of_mem_mapEntries me))).1)
  have shape : ∀ a, (∃ v₁ v₂, mapLookup R₁ a = some v₁ ∧ mapLookup R₂ a = some v₂ ∧
      mapLookup M a = if kept (a, g a v₁ v₂) then some (g a v₁ v₂) else none) ∨
      (mapLookup R₁ a = none ∧ mapLookup M a = none) ∨ (mapLookup R₂ a = none ∧ mapLookup M a = mapLookup R₁ a) := by
    intro a
    rw [look a]
    cases hit : (mapEntries R₂).find? (fun e => decide (compareExact (fuel a e.1) a e.1 = .eq)) with
    | none => exact Or.inr (Or.inr ⟨find_none hit, rfl⟩)
    | some e =>
      obtain ⟨qe, h₂⟩ := find_entry hit
      cases h₁ : mapLookup R₁ e.1 with
      | none => exact Or.inr (Or.inl ⟨by rw [mapLookup_congr qe]; exact h₁, by simp [h₁]⟩)
      | some v₁ =>
        refine Or.inl ⟨v₁, e.2, by rw [mapLookup_congr qe]; exact h₁, h₂, ?_⟩
        simp only [h₁, Option.bind_some]
        rfl
  refine ⟨M, ?_, fun q v h => ?_, fun a ρ resp => ?_, fun a h => ?_⟩
  rotate_left 3
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
    · simp [h₁]
    · cases h
    · exact h
  · simp only [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
    simpa using run
  · rcases shape q with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨-, h₃⟩ | ⟨-, h₃⟩ <;> rw [h₃] at h
    · split at h
      · cases h; exact (gspec q _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1
      · cases h
    · cases h
    · exact b₁ _ _ h
  · rcases shape a with ⟨v₁, v₂, h₁, h₂, h₃⟩ | ⟨h₁, h₃⟩ | ⟨h₂, h₃⟩
    · have sem := (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.2 ρ resp
      by_cases k : kept (a, g a v₁ v₂) = Bool.true
      · simp [evalR, h₁, h₂, h₃, k, sem]
      · have := drop_bdd (ok := P a) (gspec a _ _ (b₁ _ _ h₁) (b₂ _ _ h₂)).2.1 (by simpa using k) ρ
        simp [evalR, h₁, h₂, h₃, k, ← sem, this]
    · simp [evalR, h₁, h₃]
    · simp [evalR, h₂, h₃]

/-- Unions of maps of BDDs do not depend on the call depth. -/
theorem repr_union_uniform {P : Term → Term → Prop} {R₁ R₂ : List (Term × Term)} (b₁ : AllBddP P R₁)
    (b₂ : AllBddP P R₂) :
    ∃ M, AllBddP P M ∧ (∀ n, Elixir.Module.Types.Descr.«fun_repr_union/2» (D (n + 1)) (.map R₁) (.map R₂) =
      .ok (.map M)) ∧ (∀ a, (mapLookup R₁ a).isSome → (mapLookup M a).isSome) ∧
      ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome ∨ (mapLookup R₂ a).isSome := by
  obtain ⟨M, run, bM, -, keys⟩ := repr_union_sem 0 b₁ b₂
  let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bdd_union/2» v₁ v₂ with | .ok w => w | .error _ => .nil
  have each : ∀ n, Elixir.Module.Types.Descr.«fun_repr_union/2» (D (n + 1)) (.map R₁) (.map R₂) =
      .ok (.map (mergeList g R₁ R₂)) := by
    intro n
    have mrun := merge_with_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] R₁ R₂ g (by
      intro e me v hv
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_union/2-fun-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-fun_repr_union/2-fun-0-/3»]
      obtain ⟨r, ru, -⟩ := union_ok (b₁ _ _ hv) (b₂ _ _ (mapLookup_of_mem_mapEntries me))
      simp [g, ru])
    simp [Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», mrun]
  have same := (each 0).symm.trans run
  simp only [Except.ok.injEq, Term.map.injEq] at same
  exact ⟨M, bM, fun n => by rw [each n, same], keys⟩

/-- Intersections of maps of BDDs do not depend on the call depth. -/
theorem repr_inter_uniform {P : Term → Term → Prop} {R₁ R₂ : List (Term × Term)} (b₁ : AllBddP P R₁)
    (b₂ : AllBddP P R₂) :
    ∃ M, AllBddP P M ∧ (∀ n, Elixir.Module.Types.Descr.«fun_repr_intersection/2» (D (n + 1)) (.map R₁) (.map R₂) =
      .ok (.map M)) ∧ ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome := by
  obtain ⟨M, run, bM, -, keys⟩ := repr_inter_sem 0 b₁ b₂
  let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bdd_intersection/2» v₁ v₂ with | .ok w => w | .error _ => .nil
  have each : ∀ n, Elixir.Module.Types.Descr.«fun_repr_intersection/2» (D (n + 1)) (.map R₁) (.map R₂) =
      .ok (.map (filterList kept (interList g R₁ R₂))) := by
    intro n
    have irun := intersect_with_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-fun_repr_intersection/2-fun-0-" #[]
      R₁ R₂ g (by
        intro e me v hv
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_intersection/2-fun-0-/3».pure]
        simp only [Elixir.Module.Types.Descr.«-fun_repr_intersection/2-fun-0-/3»]
        obtain ⟨r, ru, -⟩ := inter_ok (b₁ _ _ (mapLookup_of_mem_mapEntries me)) (b₂ _ _ hv)
        simp [g, ru])
    have frun := filter_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-symmetrical_intersection/3-fun-0-" #[]
      (interList g R₁ R₂) kept (by
        intro e _
        rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
    simp [Elixir.Module.Types.Descr.«fun_repr_intersection/2»]
    unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [irun, frun]
  have same := (each 0).symm.trans run
  simp only [Except.ok.injEq, Term.map.injEq] at same
  exact ⟨M, bM, fun n => by rw [each n, same], keys⟩

/-- Differences of maps of BDDs do not depend on the call depth. -/
theorem repr_diff_uniform {P : Term → Term → Prop} {R₁ R₂ : List (Term × Term)} (b₁ : AllBddP P R₁)
    (b₂ : AllBddP P R₂) :
    ∃ M, AllBddP P M ∧ (∀ n, Elixir.Module.Types.Descr.«fun_repr_difference/2» (D n) (.map R₁) (.map R₂) =
      .ok (.map M)) ∧ ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome := by
  obtain ⟨M, run, bM, -, keys⟩ := repr_diff_sem 0 b₁ b₂
  let g : Term → Term → Term → Term := fun _ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bdd_difference/2» v₁ v₂ with | .ok w => w | .error _ => .nil
  have each : ∀ n, Elixir.Module.Types.Descr.«fun_repr_difference/2» (D n) (.map R₁) (.map R₂) =
      .ok (.map ((mapEntries R₂).foldl (differenceStep g) R₁)) := by
    intro n
    obtain ⟨M', run', -, explicit⟩ := repr_diff_fold n g (mapEntries R₂) R₁ (mapEntries_distinct R₂) (by
      intro e me v hv
      obtain ⟨r, ru, -⟩ := diff_ok (b₁ _ _ hv) (b₂ _ _ (mapLookup_of_mem_mapEntries me))
      simp [g, ru])
    rw [← explicit]
    simp only [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
    simpa using run'
  have same := (each 0).symm.trans run
  simp only [Except.ok.injEq, Term.map.injEq] at same
  exact ⟨M, bM, fun n => by rw [each n, same], keys⟩

def FunF (x : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), x = .tuple #[.atom (if pos then "union" else "negation"), .map R] ∧ AllBdd R

theorem arity_tag (pos : Bool) (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) :
    arityOf (.tuple #[.atom (if pos then "union" else "negation"), .map R]) a ρ = (pos == evalR R a ρ) := by
  cases pos <;> cases h : evalR R a ρ <;> simp_all [arityOf, evalR]

theorem size_cases (M : List (Term × Term)) :
    (Erlang.erlang.«map_size/1» (.map M) = .ok (.integer 0) ∧ ∀ q, mapLookup M q = none) ∨
      (∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s)) := by
  cases M with
  | nil => exact Or.inl ⟨rfl, fun q => by simp [mapLookup]⟩
  | cons e rest =>
    right
    refine ⟨_, ?_, rfl⟩
    simp [List.eraseDupsBy, List.eraseDupsBy.loop]
    exact fun h => loop_ne_nil _ _ _ [] h

theorem fun_union_spec (n : Nat) {x y : Term} (fx : FunF x) (fy : FunF y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom "fun") x y = .ok w ∧ FunF w ∧
      ∀ a ρ, Resp ρ → arityOf w a ρ = (arityOf x a ρ || arityOf y a ρ) := by
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  simp only [arity_tag]
  cases p₁ <;> cases p₂
  · obtain ⟨M, run, bM, sem, -⟩ := repr_inter_sem n b₁ b₂
    refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => ?_⟩
    rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 1) b₁ b₂
    refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => ?_⟩
    rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 1) b₂ b₁
    refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => ?_⟩
    rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
  · obtain ⟨M, run, bM, sem, -⟩ := repr_union_sem n b₁ b₂
    refine ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.true, M, rfl, bM⟩, fun a ρ resp => ?_⟩
    rw [arity_tag, sem a ρ resp]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl

theorem arity_union (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) :
    arityOf (.tuple #[.atom "union", .map R]) a ρ = evalR R a ρ := by simp [arityOf, evalR]

theorem arity_neg (R : List (Term × Term)) (a : Term) (ρ : Term → Bool) :
    arityOf (.tuple #[.atom "negation", .map R]) a ρ = !evalR R a ρ := by simp [arityOf, evalR]

theorem size_cons (e : Term × Term) (rest : List (Term × Term)) :
    ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map (e :: rest)) = .ok (.integer s) := by
  rcases size_cases (e :: rest) with ⟨_, none⟩ | h
  · have := none e.1
    simp [mapLookup, Std.ReflCmp.compare_self] at this
  · exact h

/-- Function results: unions whose maps of arities are empty become `0`. -/
theorem fun_finish (pos : Bool) (M : List (Term × Term)) (bM : AllBdd M) (target : Term → (Term → Bool) → Bool)
    (sem : ∀ a ρ, Resp ρ → (pos == evalR M a ρ) = target a ρ) (e : Except Exception Term)
    (he₁ : pos = Bool.false → e = .ok (.tuple #[.atom "negation", .map M]))
    (he₂ : pos = Bool.true → M = [] → e = .ok (.integer 0))
    (he₃ : pos = Bool.true → M ≠ [] → e = .ok (.tuple #[.atom "union", .map M])) :
    ∃ w, e = .ok w ∧ (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = target a ρ) ∧
      (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → target a ρ = Bool.false) := by
  cases pos
  · exact ⟨_, he₁ rfl, fun _ => ⟨⟨Bool.false, M, rfl, bM⟩, fun a ρ resp => by
      rw [arity_neg, ← sem a ρ resp]; cases evalR M a ρ <;> rfl⟩, fun k => by simp [kept] at k⟩
  · cases M with
    | nil => exact ⟨_, he₂ rfl rfl, fun k => by simp [kept] at k, fun _ a ρ resp => by
        rw [← sem a ρ resp]; simp [evalR, mapLookup]⟩
    | cons x xs => exact ⟨_, he₃ rfl (by simp), fun _ => ⟨⟨Bool.true, _, rfl, bM⟩, fun a ρ resp => by
        rw [arity_union, ← sem a ρ resp]; cases evalR _ a ρ <;> rfl⟩, fun k => by simp [kept] at k⟩

theorem fun_inter_spec (n : Nat) {x y : Term} (fx : FunF x) (fy : FunF y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") x y = .ok w ∧
      (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = (arityOf x a ρ && arityOf y a ρ)) ∧
      (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → (arityOf x a ρ && arityOf y a ρ) = Bool.false) := by
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
    intro M ne; cases M with
    | nil => exact absurd rfl ne
    | cons e rest => exact size_cons e rest
  cases p₁ <;> cases p₂
  · obtain ⟨M, run, bM, sem, -⟩ := repr_union_sem n b₁ b₂
    refine fun_finish Bool.false M bM _ (fun a ρ resp => ?_) _ (fun _ => ?_) (fun h => by cases h) (fun h => by cases h)
    · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
    · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 1) b₂ b₁
    refine fun_finish Bool.true M bM _ (fun a ρ resp => ?_) _ (fun h => by cases h) (fun _ hM => ?_) (fun _ hM => ?_)
    · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := size M hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 1) b₁ b₂
    refine fun_finish Bool.true M bM _ (fun a ρ resp => ?_) _ (fun h => by cases h) (fun _ hM => ?_) (fun _ hM => ?_)
    · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := size M hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, run, bM, sem, -⟩ := repr_inter_sem n b₁ b₂
    refine fun_finish Bool.true M bM _ (fun a ρ resp => ?_) _ (fun h => by cases h) (fun _ hM => ?_) (fun _ hM => ?_)
    · rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := size M hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

theorem allBdd_nil : AllBdd [] := fun q v h => by simp [mapLookup] at h

theorem evalR_nil (a : Term) (ρ : Term → Bool) : evalR [] a ρ = Bool.false := by simp [evalR, mapLookup]

theorem fun_neg_spec (n : Nat) {x : Term} (fx : FunF x) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun") (.tuple #[.atom "negation", .map []]) x =
        .ok w ∧
      (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = !arityOf x a ρ) ∧
      (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → arityOf x a ρ = Bool.true) := by
  have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
    intro M ne; cases M with
    | nil => exact absurd rfl ne
    | cons e rest => exact size_cons e rest
  obtain ⟨p, R, rfl, b⟩ := fx
  have flip : ∀ (w : Term), (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ →
      (!arityOf (.tuple #[.atom (if p then "union" else "negation"), .map R]) a ρ) = Bool.false) →
      kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ →
        arityOf (.tuple #[.atom (if p then "union" else "negation"), .map R]) a ρ = Bool.true := by
    intro w h k a ρ resp
    have := h k a ρ resp
    cases e : arityOf (.tuple #[.atom (if p then "union" else "negation"), .map R]) a ρ <;> simp_all
  cases p
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 1) b allBdd_nil
    have he₂ : M = [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun")
        (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map R]) = .ok (.integer 0) := by
      intro hM; subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    have he₃ : M ≠ [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun")
        (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map R]) =
          .ok (.tuple #[.atom "union", .map M]) := by
      intro hM
      obtain ⟨s, ne, sz⟩ := size M hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
    obtain ⟨w, hw, kw, dw⟩ := fun_finish Bool.true M bM (fun a ρ => !arityOf (.tuple #[.atom "negation", .map R]) a ρ)
      (fun a ρ resp => by rw [sem a ρ resp, arity_neg, evalR_nil]; cases evalR R a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => he₂ hM) (fun _ hM => he₃ hM)
    exact ⟨w, hw, kw, flip w dw⟩
  · obtain ⟨M, run, bM, sem, -⟩ := repr_union_sem n allBdd_nil b
    have he₁ : Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun")
        (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "union", .map R]) =
          .ok (.tuple #[.atom "negation", .map M]) := by
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso]
    obtain ⟨w, hw, kw, dw⟩ := fun_finish Bool.false M bM (fun a ρ => !arityOf (.tuple #[.atom "union", .map R]) a ρ)
      (fun a ρ resp => by rw [sem a ρ resp, arity_union, evalR_nil]; cases evalR R a ρ <;> rfl) _
      (fun _ => he₁) (fun h => by cases h) (fun h => by cases h)
    exact ⟨w, hw, kw, flip w dw⟩

theorem all1_true (d : Dispatcher) (f : Term) :
    ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (.atom "true")) →
      Erlang.lists.«all_1/2» d f (Term.list l) = .ok (.atom "true") := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«all_1/2»]
  | cons x xs ih =>
    intro hf
    rw [Erlang.lists.«all_1/2».eq_def]
    simp [hf x List.mem_cons_self, ih fun y m => hf y (List.mem_cons_of_mem _ m)]

theorem all_true (d : Dispatcher) (m nm : String) (caps : Array Term) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function m nm 1 caps) #[x] = .ok (.atom "true")) :
    Erlang.lists.«all/2» d (.function m nm 1 caps) (Term.list l) = .ok (.atom "true") := by
  cases l with
  | nil => simp [Erlang.lists.«all/2», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    simp [Erlang.lists.«all/2», Erlang.erlang.«is_function/2»,
      hf x List.mem_cons_self, all1_true d _ xs fun y m => hf y (List.mem_cons_of_mem _ m)]

/-- Unions of function types whose BDDs no valuation satisfies are empty. -/
theorem fun_empty_unsat (n : Nat) (R : List (Term × Term)) (bR : AllBdd R)
    (unsat : ∀ a ρ, Resp ρ → evalR R a ρ = Bool.false) :
    Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) (.tuple #[.atom "union", .map R]) (.map []) =
      .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«fun_empty?/2»
  simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind]
  have list : Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2]) =
      Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2]) := rfl
  refine all_true _ _ _ _ _ fun x m => ?_
  obtain ⟨e, me, rfl⟩ := List.mem_map.mp m
  have hv := mapLookup_of_mem_mapEntries me
  have wv := bR _ _ hv
  have uv : Unsat e.2 := fun ρ resp => by have := unsat e.1 ρ resp; simpa [evalR, hv] using this
  rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
  simp only [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2»]
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.true, Term.false,
    Erlang.maps.«put/3», Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf_unsat wv uv, Erlang.lists.«all/2»,
    Erlang.erlang.«is_function/2»]

theorem fresh_arity (R₁ R₂ : List (Term × Term)) : ∃ q, mapLookup R₁ q = none ∧ mapLookup R₂ q = none := by
  obtain ⟨q, hq⟩ := fresh_atom (R₁ ++ R₂)
  refine ⟨q, ?_, ?_⟩ <;> simp only [mapLookup, List.find?_append, Option.map_eq_none_iff, Option.or_eq_none_iff] at hq ⊢
  · exact hq.1
  · exact hq.2

/-- A union of function types whose arities no valuation satisfies is `0` or empty. -/
theorem fun_union_empty (n : Nat) (M : List (Term × Term)) (bM : AllBdd M) (unsat : ∀ a ρ, Resp ρ → evalR M a ρ = Bool.false)
    (e : Except Exception Term) (he₂ : M = [] → e = .ok (.integer 0))
    (he₃ : M ≠ [] → e = .ok (.tuple #[.atom "union", .map M])) :
    ∃ w, e = .ok w ∧ (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
      Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true")) := by
  cases M with
  | nil => exact ⟨_, he₂ rfl, Or.inl rfl⟩
  | cons x xs => exact ⟨_, he₃ (by simp), Or.inr (Or.inr (fun_empty_unsat n _ bM unsat))⟩

theorem fun_sub_spec (n : Nat) {a : Term} (fa : FunF a) (b : Option Term) (fb : ∀ y, b = some y → FunF y)
    (incl : ∀ q ρ, Resp ρ → arityOf a q ρ = Bool.true → b.elim Bool.false (fun y => arityOf y q ρ) = Bool.true) :
    (∀ y, b = some y → ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun") a y = .ok w ∧
      (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
        Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true"))) ∧
    (b = none → Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) a (.map []) = .ok (.atom "true")) := by
  have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
    intro M ne; cases M with
    | nil => exact absurd rfl ne
    | cons e rest => exact size_cons e rest
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fa
  refine ⟨fun y hb => ?_, fun hb => ?_⟩
  · subst hb
    obtain ⟨p₂, R₂, rfl, b₂⟩ := fb _ rfl
    have incl' : ∀ q ρ, Resp ρ → (p₁ == evalR R₁ q ρ) = Bool.true → (p₂ == evalR R₂ q ρ) = Bool.true := by
      intro q ρ resp h
      have := incl q ρ resp (by rw [arity_tag]; exact h)
      simpa [Option.elim, arity_tag] using this
    have finish : ∀ (M : List (Term × Term)), AllBdd M →
        (∀ q ρ, Resp ρ → evalR M q ρ = Bool.false) →
        (M = [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun")
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂]) = .ok (.integer 0)) →
        (M ≠ [] → Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun")
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂]) = .ok (.tuple #[.atom "union", .map M])) →
        ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun")
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂]) = .ok w ∧
          (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
            Elixir.Module.Types.Descr.«fun_empty?/2» (D (n + 2)) w (.map []) = .ok (.atom "true")) :=
      fun M bM unsat he₂ he₃ => fun_union_empty n M bM unsat _ he₂ he₃
    cases p₁ <;> cases p₂
    · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 2) b₂ b₁
      refine finish M bM (fun q ρ resp => ?_) (fun hM => ?_) (fun hM => ?_)
      · have := incl' q ρ resp
        rw [sem q ρ resp]
        cases h₁ : evalR R₁ q ρ <;> cases h₂ : evalR R₂ q ρ <;> simp_all
      · subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
      · obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
    · exfalso
      obtain ⟨q, h₁, h₂⟩ := fresh_arity R₁ R₂
      have := incl' q _ (resp_const Bool.true)
      simp [evalR, h₁, h₂] at this
    · obtain ⟨M, run, bM, sem, -⟩ := repr_inter_sem (n + 1) b₁ b₂
      refine finish M bM (fun q ρ resp => ?_) (fun hM => ?_) (fun hM => ?_)
      · have := incl' q ρ resp
        rw [sem q ρ resp]
        cases h₁ : evalR R₁ q ρ <;> cases h₂ : evalR R₂ q ρ <;> simp_all
      · subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
      · obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
    · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 2) b₁ b₂
      refine finish M bM (fun q ρ resp => ?_) (fun hM => ?_) (fun hM => ?_)
      · have := incl' q ρ resp
        rw [sem q ρ resp]
        cases h₁ : evalR R₁ q ρ <;> cases h₂ : evalR R₂ q ρ <;> simp_all
      · subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
      · obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · subst hb
    cases p₁
    · exfalso
      obtain ⟨q, h₁, -⟩ := fresh_arity R₁ R₁
      have := incl q _ (resp_const Bool.true) (by rw [arity_tag]; simp [evalR, h₁])
      simp [Option.elim] at this
    · refine fun_empty_unsat n R₁ b₁ fun q ρ resp => ?_
      cases h : evalR R₁ q ρ
      · rfl
      · have := incl q ρ resp (by rw [arity_tag]; simp [h])
        simp [Option.elim] at this

/-! Types whose fields have the semantics above. -/

def names : List String := ["bitmap", "atom", "fun", "list", "tuple", "map"]

def FieldK (E : Term → Prop) (name : String) (x : Term) : Prop :=
  (name = "bitmap" ∧ BitField x) ∨ (name = "atom" ∧ AtomF x) ∨ (name = "fun" ∧ FunF x) ∨
    (name = "list" ∧ ListField x) ∨ (name = "tuple" ∧ OField (TupleOk E) x) ∨ (name = "map" ∧ OField (MapOk E) x)

structure Sem (E : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → ∃ name ∈ names, q = .atom name
  fields : ∀ name x, mapLookup X (.atom name) = some x → FieldK E name x

def dn (name : String) (x : Option Term) (p : Point) : Bool :=
  match x with
  | none => Bool.false
  | some x => if name = "bitmap" then bitOf x p.1 else if name = "atom" then amemV (some x) p.2.1
      else if name = "fun" then arityOf x p.2.1 p.2.2 else if name = "list" then denL x p.2.2 else denO x p.2.2

def PtOk (name : String) (p : Point) : Prop :=
  Resp p.2.2 ∧ (name = "bitmap" → p.1 < 8) ∧ (name = "tuple" → Real p.2.2)

def topL (x : Option Term) : Bool :=
  match x with
  | none => Bool.false
  | some x => isListTop x

theorem Sem.static {X : List (Term × Term)} (s : Sem E X) : mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    obtain ⟨name, m, e⟩ := s.keys (.atom "dynamic") (by rw [h]; rfl)
    simp only [Term.atom.injEq] at e
    subst e
    simp [names] at m

/-- The fields of a union of static types, at any key. -/
theorem union_any (depth : Nat) (L R : List (Term × Term))
    (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
    (keysR : ∀ q, (mapLookup R q).isSome → ∃ name, q = .atom name)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (D depth) q x y = .ok u) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
      ∀ q, (mapLookup R q = Option.none → mapLookup U q = mapLookup L q) ∧
        (∀ y, mapLookup R q = some y → mapLookup L q = Option.none → mapLookup U q = some y) ∧
        (∀ x y u, mapLookup L q = some x → mapLookup R q = some y →
          Elixir.Module.Types.Descr.«bare_union/3» (D depth) q x y = .ok u → mapLookup U q = some u) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_union/3» (D depth) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, Elixir.Module.Types.Descr.«bare_union/3» (D depth) q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  obtain ⟨U, run, look⟩ : ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
      ∀ q, mapLookup U q =
        match (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => some (match mapLookup L e.1 with | some x => g e.1 x e.2 | none => e.2)
        | none => mapLookup L q := by
    unfold Elixir.Module.Types.Descr.«bare_union/2»
    simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
    by_cases emptyL : L = []
    · subst emptyL
      refine ⟨R, by simp, fun q => ?_⟩
      cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | none => rw [find_none hit]; simp [mapLookup]
      | some e => rw [(find_entry hit).2]; simp [mapLookup]
    by_cases emptyR : R = []
    · subst emptyR
      exact ⟨L, by simp [emptyL], fun q => by simp [mapLookup]⟩
    simp only [emptyL, emptyR]
    unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
    obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup (D (depth + 1)) "Elixir.Module.Types.Descr" "bare_union" #[]
      L R g (by
        intro e me x hx
        have hy := mapLookup_of_mem_mapEntries me
        obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
        rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure, ru, value _ _ _ _ ru])
    exact ⟨out, by simpa using run, look⟩
  refine ⟨U, run, fun q => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rfl
    | some e => rw [(find_entry hit).2] at hR; cases hR
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit] at hR; cases hR
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [h] at hR; cases hR
      simp [← mapLookup_congr qe, hL]
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit] at hR; cases hR
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [h] at hR; cases hR
      obtain ⟨name, hname⟩ := keysR e.1 (by rw [← mapLookup_congr qe, h]; rfl)
      rw [hname] at qe
      obtain rfl := (compareExact_eq_atom q name).mp qe
      simp [hname, hL, value _ _ _ _ ru]

theorem dn_bitmap (x : Term) (p : Point) : dn "bitmap" (some x) p = bitOf x p.1 := by simp [dn]
theorem dn_atom (x : Term) (p : Point) : dn "atom" (some x) p = amemV (some x) p.2.1 := by simp [dn]
theorem dn_fun (x : Term) (p : Point) : dn "fun" (some x) p = arityOf x p.2.1 p.2.2 := by simp [dn]
theorem dn_list (x : Term) (p : Point) : dn "list" (some x) p = denL x p.2.2 := by simp [dn]
theorem dn_tuple (x : Term) (p : Point) : dn "tuple" (some x) p = denO x p.2.2 := by simp [dn]
theorem dn_map (x : Term) (p : Point) : dn "map" (some x) p = denO x p.2.2 := by simp [dn]
theorem dn_none (name : String) (p : Point) : dn name Option.none p = Bool.false := rfl

theorem field_union (n : Nat) {name : String} {x y : Term} (fx : FieldK E name x) (fy : FieldK E name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y = .ok w ∧ FieldK E name w ∧
      (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
      (name = "list" → isListTop w = (isListTop x || isListTop y)) := by
  rcases fx with ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ <;>
    rcases fy with ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ <;>
    (try simp only [String.reduceEq] at h) <;> (try clear h)
  · obtain ⟨w, run, fw, sem⟩ := bit_union (D (n + 1)) fx fy
    exact ⟨w, run, Or.inl ⟨rfl, fw⟩, fun p _ => by simp [dn_bitmap, sem], fun h => by simp at h⟩
  · obtain ⟨w, run, fw, sem⟩ := atom_union_spec (D (n + 1)) fx fy
    exact ⟨w, run, Or.inr (Or.inl ⟨rfl, fw⟩), fun p _ => by simp [dn_atom, sem], fun h => by simp at h⟩
  · obtain ⟨w, run, fw, sem⟩ := fun_union_spec n fx fy
    exact ⟨w, run, Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), fun p ok => by simp [dn_fun, sem _ _ ok.1], fun h => by simp at h⟩
  · obtain ⟨w, run, fw, sem, top⟩ := list_union_spec fx fy
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))),
      fun p ok => by simp [dn_list, sem _ ok.1], fun _ => top⟩
  · obtain ⟨w, run, fw, sem⟩ := open_union_spec tupleOk_not _ tuple_union_shape.1 tuple_union_shape.2.1
      tuple_union_shape.2.2 fx fy
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))),
      fun p ok => by simp [dn_tuple, sem _ ok.1], fun h => by simp at h⟩
  · obtain ⟨w, run, fw, sem⟩ := open_union_spec mapOk_not _ map_union_shape.1 map_union_shape.2.1
      map_union_shape.2.2 fx fy
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw⟩)))),
      fun p ok => by simp [dn_map, sem _ ok.1], fun h => by simp at h⟩

/-- The fields of the top type. -/
def TopAt (name : String) (t : Term) : Prop :=
  (name = "bitmap" ∧ t = .integer 255) ∨ (name = "atom" ∧ t = .tuple #[.atom "negation", .map []]) ∨
    (name = "fun" ∧ t = .tuple #[.atom "negation", .map []]) ∨
    (name = "list" ∧ t = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
    (name = "tuple" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
    (name = "map" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil])

theorem field_neg (hterm : E (.atom "term")) (n : Nat) {name : String} {t x : Term} (ht : TopAt name t) (fx : FieldK E name x) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom name) t x = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldK E name w ∧
        (∀ p, PtOk name p → dn name (some w) p = !dn name (some x) p) ∧ (name = "list" → isListTop w = Bool.false)) ∧
      (kept (.atom name, w) = Bool.false → ∀ p, PtOk name p → dn name (some x) p = Bool.true) := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases fx with ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ | ⟨h, fx⟩ <;>
    (try simp only [String.reduceEq] at h) <;> (try clear h)
  · obtain ⟨w, run, k, d⟩ := bit_neg (D (n + 1)) fx
    exact ⟨w, run, fun kw => ⟨Or.inl ⟨rfl, (k kw).1⟩, fun p ok => by simp [dn_bitmap, (k kw).2 _ (ok.2.1 rfl)],
      fun h => by simp at h⟩, fun kw p ok => by simp [dn_bitmap, d kw _ (ok.2.1 rfl)]⟩
  · obtain ⟨w, run, k, d⟩ := atom_neg_spec (D (n + 1)) fx
    exact ⟨w, run, fun kw => ⟨Or.inr (Or.inl ⟨rfl, (k kw).1⟩), fun p ok => by simp [dn_atom, (k kw).2],
      fun h => by simp at h⟩, fun kw p ok => by simp [dn_atom, d kw]⟩
  · obtain ⟨w, run, k, d⟩ := fun_neg_spec n fx
    exact ⟨w, run, fun kw => ⟨Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)), fun p ok => by simp [dn_fun, (k kw).2 _ _ ok.1],
      fun h => by simp at h⟩, fun kw p ok => by simp [dn_fun, d kw _ _ ok.1]⟩
  · obtain ⟨w, run, k, d⟩ := list_neg_spec fx
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, (k kw).1⟩))), fun p ok => by simp [dn_list, (k kw).2.2 _ ok.1], fun _ => (k kw).2.1⟩,
      fun kw p ok => by simp [dn_list, d kw _ ok.1]⟩
  · obtain ⟨w, run, k, d⟩ := tuple_neg_spec hterm fx
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_tuple, (k kw).2 _ ok.1 (ok.2.2 rfl)], fun h => by simp at h⟩,
      fun kw p ok => by simp [dn_tuple, d kw _ ok.1 (ok.2.2 rfl)]⟩
  · obtain ⟨w, run, k, d⟩ := map_neg_spec fx
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_map, (k kw).2 _ ok.1], fun h => by simp at h⟩,
      fun kw p ok => by simp [dn_map, d kw _ ok.1]⟩

theorem field_inter (n : Nat) {name : String} {x y : Term} (fx : FieldK E name x) (fy : FieldK E name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldK E name w ∧
        (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p && dn name (some y) p)) ∧
        (name = "list" → isListTop w = (isListTop x && isListTop y))) ∧
      (kept (.atom name, w) = Bool.false → (∀ p, PtOk name p → (dn name (some x) p && dn name (some y) p) = Bool.false) ∧
        (name = "list" → (isListTop x && isListTop y) = Bool.false)) := by
  rcases fx with ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ <;>
    rcases fy with ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ | ⟨h, fy⟩ <;>
    (try simp only [String.reduceEq] at h) <;> (try clear h)
  · obtain ⟨w, run, k, d⟩ := bit_inter (D (n + 1)) fx fy
    exact ⟨w, run, fun kw => ⟨Or.inl ⟨rfl, (k kw).1⟩, fun p _ => by simp [dn_bitmap, (k kw).2], fun h => by simp at h⟩,
      fun kw => ⟨fun p _ => by simp [dn_bitmap, d kw], fun h => by simp at h⟩⟩
  · obtain ⟨w, run, k, d⟩ := atom_inter_spec (D (n + 1)) fx fy
    exact ⟨w, run, fun kw => ⟨Or.inr (Or.inl ⟨rfl, (k kw).1⟩), fun p _ => by simp [dn_atom, (k kw).2],
      fun h => by simp at h⟩, fun kw => ⟨fun p _ => by simp [dn_atom, d kw], fun h => by simp at h⟩⟩
  · obtain ⟨w, run, k, d⟩ := fun_inter_spec n fx fy
    exact ⟨w, run, fun kw => ⟨Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)), fun p ok => by simp [dn_fun, (k kw).2 _ _ ok.1],
      fun h => by simp at h⟩, fun kw => ⟨fun p ok => by simp [dn_fun, d kw _ _ ok.1], fun h => by simp at h⟩⟩
  · obtain ⟨w, run, k, d⟩ := list_inter_spec fx fy
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, (k kw).1⟩))), fun p ok => by simp [dn_list, (k kw).2.1 _ ok.1], fun _ => (k kw).2.2⟩,
      fun kw => ⟨fun p ok => by simp [dn_list, (d kw).1 _ ok.1], fun _ => (d kw).2⟩⟩
  · obtain ⟨w, run, k, d⟩ := open_inter_spec tupleOk_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
      tuple_inter_shape.2.2 (.atom "tuple") fx fy
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_tuple, (k kw).2 _ ok.1], fun h => by simp at h⟩,
      fun kw => ⟨fun p ok => by simp [dn_tuple, d kw _ ok.1], fun h => by simp at h⟩⟩
  · obtain ⟨w, run, k, d⟩ := open_inter_spec mapOk_not _ map_inter_shape.1 map_inter_shape.2.1
      map_inter_shape.2.2 (.atom "map") fx fy
    exact ⟨w, by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => ⟨Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨rfl, (k kw).1⟩)))), fun p ok => by simp [dn_map, (k kw).2 _ ok.1], fun h => by simp at h⟩,
      fun kw => ⟨fun p ok => by simp [dn_map, d kw _ ok.1], fun h => by simp at h⟩⟩

theorem dn_elim (name : String) (x : Option Term) (p : Point) :
    dn name x p = x.elim Bool.false (fun y => dn name (some y) p) := by cases x <;> rfl

theorem field_sub (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K + 3 ≤ m) {name : String} {a : Term} (fa : FieldK E name a) (B : List (Term × Term))
    (fb : ∀ y, mapLookup B (.atom name) = some y → FieldK E name y)
    (incl : ∀ p, PtOk name p → dn name (some a) p = Bool.true → dn name (mapLookup B (.atom name)) p = Bool.true)
    (side : name = "list" → ∀ y, mapLookup B (.atom name) = some y → isListTop y = Bool.true → isListTop a = Bool.true) :
    KeySub (D m) B (.atom name) a := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  have kind : ∀ {P : Term → Prop}, (∀ y, FieldK E name y → P y) → ∀ y, mapLookup B (.atom name) = some y → P y :=
    fun h y hy => h y (fb y hy)
  rcases fa with ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩ | ⟨rfl, fa⟩
  · have fb' : ∀ y, mapLookup B (.atom "bitmap") = some y → BitField y := kind fun y h => by
      rcases h with ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
    obtain ⟨some, notNone⟩ := bit_sub (D (n + 3)) fa _ fb' fun i lt h => by
      have := incl (i, .nil, fun _ => Bool.true) ⟨resp_const _, fun _ => lt, fun e => by simp at e⟩ (by simpa [dn_bitmap])
      rw [dn_elim] at this
      simpa [dn_bitmap] using this
    cases hb : mapLookup B (.atom "bitmap") with
    | none => exact absurd hb notNone
    | some y => exact Or.inl ⟨y, _, hb, some y hb, Or.inl rfl⟩
  · have fb' : ∀ y, mapLookup B (.atom "atom") = some y → AtomF y := kind fun y h => by
      rcases h with ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
    obtain ⟨some, notNone⟩ := atom_sub_spec (D (n + 3)) fa _ fb' fun q h => by
      have := incl (0, q, fun _ => Bool.true) ⟨resp_const _, fun e => by simp at e, fun e => by simp at e⟩
        (by simpa [dn_atom])
      rw [dn_elim] at this
      simpa [dn_atom] using this
    cases hb : mapLookup B (.atom "atom") with
    | none => exact absurd hb notNone
    | some y => exact Or.inl ⟨y, _, hb, some y hb, Or.inl rfl⟩
  · have fb' : ∀ y, mapLookup B (.atom "fun") = some y → FunF y := kind fun y h => by
      rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
    obtain ⟨some, none⟩ := fun_sub_spec (n + 1) fa _ fb' fun q ρ resp h => by
      have := incl (0, q, ρ) ⟨resp, fun e => by simp at e, fun e => by simp at e⟩ (by simpa [dn_fun])
      rw [dn_elim] at this
      simpa [dn_fun] using this
    cases hb : mapLookup B (.atom "fun") with
    | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
    | some y =>
      obtain ⟨w, run, h⟩ := some y hb
      refine Or.inl ⟨y, w, hb, run, ?_⟩
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h
  · have fb' : ∀ y, mapLookup B (.atom "list") = some y → ListField y := kind fun y h => by
      rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
    obtain ⟨some, none⟩ := list_sub_spec (D (n + 3)) fa _ fb' (fun ρ resp h => by
      have := incl (0, .nil, ρ) ⟨resp, fun e => by simp at e, fun e => by simp at e⟩ (by simpa [dn_list])
      rw [dn_elim] at this
      simpa [dn_list] using this) (side rfl)
    cases hb : mapLookup B (.atom "list") with
    | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
    | some y =>
      obtain ⟨w, run, h⟩ := some y hb
      refine Or.inl ⟨y, w, hb, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, ?_⟩
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h
  · have fb' : ∀ y, mapLookup B (.atom "tuple") = some y → OField (TupleOk E) y := kind fun y h => by
      rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩ <;> first | exact h | simp at e
    obtain ⟨some, none⟩ := tuple_sub_spec ops dops (m := n + 3) (by omega) fa _ fb' fun ρ resp real h => by
      have := incl (0, .nil, ρ) ⟨resp, fun e => by simp at e, fun _ => real⟩ (by simpa [dn_tuple])
      rw [dn_elim] at this
      simpa [dn_tuple] using this
    cases hb : mapLookup B (.atom "tuple") with
    | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
    | some y =>
      obtain ⟨w, run, h⟩ := some y hb
      refine Or.inl ⟨y, w, hb, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, ?_⟩
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h
  · have fb' : ∀ y, mapLookup B (.atom "map") = some y → OField (MapOk E) y := kind fun y h => by
      rcases h with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ <;> first | exact h | simp at e
    obtain ⟨some, none⟩ := map_sub_spec ops (m := n + 3) (by omega) fa _ fb' fun ρ resp h => by
      have := incl (0, .nil, ρ) ⟨resp, fun e => by simp at e, fun e => by simp at e⟩ (by simpa [dn_map])
      rw [dn_elim] at this
      simpa [dn_map] using this
    cases hb : mapLookup B (.atom "map") with
    | none => exact Or.inr ⟨hb, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using none hb⟩
    | some y =>
      obtain ⟨w, run, h⟩ := some y hb
      refine Or.inl ⟨y, w, hb, by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run, ?_⟩
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h

/-- A type is a subtype of another when each field holds less, and the right type lacks the top list type
unless the left type has it too. -/
theorem sem_sub (ops : ElemOk E K) (dops : ElemDiff E K) {m : Nat} (hm : K + 3 ≤ m) (A B : List (Term × Term)) (sA : Sem E A) (sB : Sem E B)
    (incl : ∀ name ∈ names, ∀ p, PtOk name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true)
    (side : topL (mapLookup B (.atom "list")) = Bool.true → topL (mapLookup A (.atom "list")) = Bool.true) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) = .ok (.atom "true") := by
  refine subtype_keys _ A B sA.static sB.static fun e member => ?_
  have hA := mapLookup_of_mem_mapEntries member
  obtain ⟨name, m, hname⟩ := sA.keys e.1 (by simp [hA])
  rw [hname] at hA ⊢
  have fa := sA.fields name e.2 hA
  refine field_sub ops dops hm fa B (sB.fields name) (fun p ok h => incl name m p ok (by rw [hA]; exact h))
    fun hl y hy top => ?_
  subst hl
  have := side (by simp [topL, hy, top])
  simpa [topL, hA] using this

theorem sem_union (δ : Nat) (L R : List (Term × Term)) (sL : Sem E L) (sR : Sem E R) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map L) (.map R) = .ok (.map U) ∧ Sem E U ∧
      (∀ name, ∀ p, PtOk name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p)) ∧
      topL (mapLookup U (.atom "list")) = (topL (mapLookup L (.atom "list")) || topL (mapLookup R (.atom "list"))) ∧
      (L ≠ [] → U ≠ []) ∧
      (mapLookup U (.atom "list")).isNone =
        ((mapLookup L (.atom "list")).isNone && (mapLookup R (.atom "list")).isNone) := by
  have calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (D (δ + 99)) q x y = .ok u := by
    intro q x y hx hy
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := field_union (δ + 98) (sL.fields name x hx) (sR.fields name y hy)
    exact ⟨w, run⟩
  obtain ⟨U, run, look⟩ := union_any (δ + 99) L R sL.static sR.static
    (fun q h => by obtain ⟨name, -, e⟩ := sR.keys q h; exact ⟨name, e⟩) calls
  -- What the union holds at each field name.
  have at_name : ∀ name, (mapLookup R (.atom name) = Option.none ∧ mapLookup U (.atom name) = mapLookup L (.atom name)) ∨
      (∃ y, mapLookup L (.atom name) = Option.none ∧ mapLookup R (.atom name) = some y ∧
        mapLookup U (.atom name) = some y) ∨
      (∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup U (.atom name) = some w ∧ FieldK E name w ∧
        (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
        (name = "list" → isListTop w = (isListTop x || isListTop y))) := by
    intro name
    cases hR : mapLookup R (.atom name) with
    | none => exact Or.inl ⟨rfl, (look _).1 hR⟩
    | some y =>
      cases hL : mapLookup L (.atom name) with
      | none => exact Or.inr (Or.inl ⟨y, rfl, rfl, (look _).2.1 y hR hL⟩)
      | some x =>
        obtain ⟨w, run, fw, sem, top⟩ := field_union (δ + 98) (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, w, rfl, rfl, (look _).2.2 x y w hL hR run, fw, sem, top⟩)
  refine ⟨U, run, ⟨fun q h => ?_, fun name w hw => ?_⟩, fun name p ok => ?_, ?_, fun ne => ?_, ?_⟩
  rotate_right
  · rcases at_name "list" with ⟨hR, hU⟩ | ⟨y, hL, hR, hU⟩ | ⟨x, y, w, hL, hR, hU, -⟩
    · simp [hU, hR]
    · simp [hU, hL, hR]
    · simp [hU, hL, hR]
  · cases hR : mapLookup R q with
    | none =>
      rw [(look q).1 hR] at h
      exact sL.keys q h
    | some y => exact sR.keys q (by simp [hR])
  · rcases at_name name with ⟨-, hU⟩ | ⟨y, -, hR, hU⟩ | ⟨x, y, w', -, -, hU, fw, -⟩ <;> rw [hU] at hw
    · exact sL.fields name w hw
    · rw [← Option.some.inj hw]; exact sR.fields name y hR
    · rw [← Option.some.inj hw]; exact fw
  · rcases at_name name with ⟨hR, hU⟩ | ⟨y, hL, hR, hU⟩ | ⟨x, y, w, hL, hR, hU, -, sem, -⟩
    · simp [hU, hR, dn_none]
    · simp [hU, hL, hR, dn_none]
    · rw [hU, hL, hR, sem p ok]
  · rcases at_name "list" with ⟨hR, hU⟩ | ⟨y, hL, hR, hU⟩ | ⟨x, y, w, hL, hR, hU, -, -, top⟩
    · simp [hU, hR, topL]
    · simp [hU, hL, hR, topL]
    · simp [hU, hL, hR, topL, top rfl]
  · intro empty
    subst empty
    cases L with
    | nil => exact ne rfl
    | cons e rest =>
      obtain ⟨name, -, he⟩ := sL.keys e.1 (by simp [mapLookup, Std.ReflCmp.compare_self])
      rcases at_name name with ⟨-, hU⟩ | ⟨y, -, -, hU⟩ | ⟨x, y, w, -, -, hU, -⟩ <;> simp [mapLookup] at hU
      have : mapLookup (e :: rest) (.atom name) ≠ Option.none := by
        rw [← he]; simp [mapLookup, Std.ReflCmp.compare_self]
      exact this hU.symm

theorem term_top {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (h : mapLookup T q = some t) : ∃ name ∈ names, q = .atom name ∧ TopAt name t := by
  rcases term_keys term h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨"bitmap", by simp [names], rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨"atom", by simp [names], rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨"fun", by simp [names], rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · exact ⟨"list", by simp [names], rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · exact ⟨"tuple", by simp [names], rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  · exact ⟨"map", by simp [names], rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

theorem term_at {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {name : String} (m : name ∈ names) : ∃ t, mapLookup T (.atom name) = some t ∧ TopAt name t := by
  simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
  cases term
  simp only [names, List.mem_cons, List.mem_nil_iff, or_false] at m
  rcases m with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [mapLookup], Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, by simp [mapLookup], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  · exact ⟨_, by simp [mapLookup], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

theorem top_field {name : String} {t : Term} (ht : TopAt name t) :
    FieldK E name t ∧ (∀ p, PtOk name p → dn name (some t) p = Bool.true) ∧
      (name = "list" → isListTop t = Bool.true) := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨Or.inl ⟨rfl, 255, rfl, by decide, by decide⟩, fun p ok => ?_, fun h => by simp at h⟩
    have lt := ok.2.1 rfl
    have bits : ∀ i, i < 8 → (255 : Nat).testBit i = Bool.true := by decide
    simpa [dn_bitmap, bitOf] using bits p.1 lt
  · refine ⟨Or.inr (Or.inl ⟨rfl, ⟨Bool.false, [], rfl, no_atoms⟩, .nil, by simp [amemV, mapLookup]⟩),
      fun p _ => by simp [dn_atom, amemV, mapLookup], fun h => by simp at h⟩
  · refine ⟨Or.inr (Or.inr (Or.inl ⟨rfl, Bool.false, [], rfl, allBdd_nil⟩)), fun p _ => by
      simp [dn_fun, arityOf, mapLookup], fun h => by simp at h⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩))), fun p _ => by simp [dn_list, denL_top],
      fun _ => by simp [isListTop]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩)))), fun p _ => by simp [dn_tuple, denO_top],
      fun h => by simp at h⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨_, rfl⟩⟩)))), fun p _ => by simp [dn_map, denO_top],
      fun h => by simp at h⟩

theorem sem_neg (δ : Nat) (hterm : E (.atom "term")) (X : List (Term × Term)) (sX : Sem E X) (nonempty : X ≠ []) :
    ∃ N, Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map X) = .ok (.map N) ∧ Sem E N ∧
      (∀ name ∈ names, ∀ p, PtOk name p → dn name (mapLookup N (.atom name)) p = !dn name (mapLookup X (.atom name)) p) ∧
      topL (mapLookup N (.atom "list")) = (mapLookup X (.atom "list")).isNone := by
  obtain ⟨T, term, -, -, -, termDynamic⟩ := unfolded_term_fields
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (D (δ + 98)) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y w, Elixir.Module.Types.Descr.«bare_difference/3» (D (δ + 98)) q x y = .ok w → g q x y = w := by
    intro q x y w run; simp [g, run]
  obtain ⟨N, fold, lookN, -⟩ := difference_fold (δ + 98) (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries X) T (mapEntries_distinct X) (by
      intro e member v₁ found
      have hy := mapLookup_of_mem_mapEntries member
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure]
      obtain ⟨name, -, he, ht⟩ := term_top term found
      rw [he] at hy found ⊢
      obtain ⟨w, run, -⟩ := field_neg hterm (δ + 97) ht (sX.fields name e.2 hy)
      rw [run, value _ _ _ _ run])
  have run : Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map X) = .ok (.map N) := by
    simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map sX.static, nonempty]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
    simpa using fold
  -- What the negation holds at each field name.
  have at_name : ∀ name ∈ names, ∃ t, TopAt name t ∧
      ((mapLookup X (.atom name) = Option.none ∧ mapLookup N (.atom name) = some t) ∨
      (∃ x w, mapLookup X (.atom name) = some x ∧
        Elixir.Module.Types.Descr.«bare_difference/3» (D (δ + 98)) (.atom name) t x = .ok w ∧
        mapLookup N (.atom name) = if kept (.atom name, w) then some w else Option.none)) := by
    intro name m
    obtain ⟨t, hT, ht⟩ := term_at term m
    refine ⟨t, ht, ?_⟩
    rw [lookN, find_atom]
    cases hX : mapLookup X (.atom name) with
    | none => exact Or.inl ⟨rfl, hT⟩
    | some x =>
      obtain ⟨w, run, -⟩ := field_neg hterm (δ + 97) ht (sX.fields name x hX)
      exact Or.inr ⟨x, w, rfl, run, by simp [hT, value _ _ _ _ run]⟩
  have keysN : ∀ q, (mapLookup N q).isSome → ∃ name ∈ names, q = .atom name := by
    intro q h
    rw [lookN] at h
    cases hit : (mapEntries X).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none =>
      rw [hit] at h
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨name, m, rfl, -⟩ := term_top term ht
      exact ⟨name, m, rfl⟩
    | some e =>
      rw [hit] at h
      obtain ⟨qe, -⟩ := find_entry hit
      cases ht : mapLookup T e.1 with
      | none => simp [ht] at h
      | some t =>
        obtain ⟨name, m, he, -⟩ := term_top term ht
        rw [he] at qe
        exact ⟨name, m, (compareExact_eq_atom q name).mp qe⟩
  refine ⟨N, run, ⟨keysN, fun name w hw => ?_⟩, fun name m p ok => ?_, ?_⟩
  · obtain ⟨name', m, e⟩ := keysN (.atom name) (by simp [hw])
    simp only [Term.atom.injEq] at e
    subst e
    rcases at_name name m with ⟨t, ht, ⟨-, hN⟩ | ⟨x, w', hX, run', hN⟩⟩
    · rw [hN] at hw; rw [← Option.some.inj hw]; exact (top_field (E := E) ht).1
    · obtain ⟨w'', run'', k, -⟩ := field_neg hterm (δ + 97) ht (sX.fields name x hX)
      have e : w'' = w' := by rw [run''] at run'; exact Except.ok.inj run'
      subst e
      by_cases kw : kept (.atom name, w'') = Bool.true
      · simp only [kw, ite_true] at hN
        rw [hN] at hw; rw [← Option.some.inj hw]; exact (k kw).1
      · simp [kw] at hN; rw [hN] at hw; cases hw
  · rcases at_name name m with ⟨t, ht, ⟨hX, hN⟩ | ⟨x, w', hX, run', hN⟩⟩
    · rw [hN, hX, (top_field (E := E) ht).2.1 p ok]; rfl
    · obtain ⟨w'', run'', k, d⟩ := field_neg hterm (δ + 97) ht (sX.fields name x hX)
      have e : w'' = w' := by rw [run''] at run'; exact Except.ok.inj run'
      subst e
      by_cases kw : kept (.atom name, w'') = Bool.true
      · simp only [kw, ite_true] at hN
        rw [hN, hX, (k kw).2.1 p ok]
      · simp only [kw, Bool.false_eq_true, ite_false] at hN
        rw [hN, hX, dn_none, d (by simpa using kw) p ok]; rfl
  · rcases at_name "list" (by simp [names]) with ⟨t, ht, ⟨hX, hN⟩ | ⟨x, w', hX, run', hN⟩⟩
    · simp [hN, hX, topL, (top_field (E := E) ht).2.2 rfl]
    · obtain ⟨w'', run'', k, -⟩ := field_neg hterm (δ + 97) ht (sX.fields "list" x hX)
      have e : w'' = w' := by rw [run''] at run'; exact Except.ok.inj run'
      subst e
      by_cases kw : kept (.atom "list", w'') = Bool.true
      · simp [kw, hN, hX, topL, (k kw).2.2 rfl]
      · simp [kw, hN, hX, topL]

theorem sem_inter (δ : Nat) (L R : List (Term × Term)) (sL : Sem E L) (sR : Sem E R) :
    ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.map L) (.map R) = .ok (.map I) ∧ Sem E I ∧
      (∀ name, ∀ p, PtOk name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p)) ∧
      topL (mapLookup I (.atom "list")) = (topL (mapLookup L (.atom "list")) && topL (mapLookup R (.atom "list"))) := by
  obtain ⟨I, run, look, keysI⟩ := inter_lookup (δ + 99) L R sL.static sR.static (by
    intro q x y hx hy
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := field_inter (δ + 98) (sL.fields name x hx) (sR.fields name y hy)
    exact ⟨w, run⟩)
  have at_name : ∀ name, ((mapLookup L (.atom name) = Option.none ∨ mapLookup R (.atom name) = Option.none) ∧
      mapLookup I (.atom name) = Option.none) ∨
      (∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup I (.atom name) = (if kept (.atom name, w) then some w else Option.none) ∧
        (kept (.atom name, w) = Bool.true → FieldK E name w ∧
          (∀ p, PtOk name p → dn name (some w) p = (dn name (some x) p && dn name (some y) p)) ∧
          (name = "list" → isListTop w = (isListTop x && isListTop y))) ∧
        (kept (.atom name, w) = Bool.false →
          (∀ p, PtOk name p → (dn name (some x) p && dn name (some y) p) = Bool.false) ∧
          (name = "list" → (isListTop x && isListTop y) = Bool.false))) := by
    intro name
    cases hL : mapLookup L (.atom name) with
    | none => exact Or.inl ⟨Or.inl rfl, (look name).1 hL⟩
    | some x =>
      cases hR : mapLookup R (.atom name) with
      | none => exact Or.inl ⟨Or.inr rfl, (look name).2.1 hR⟩
      | some y =>
        obtain ⟨w, run, k, d⟩ := field_inter (δ + 98) (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr ⟨x, y, w, rfl, rfl, (look name).2.2 x y w hL hR run, k, d⟩
  refine ⟨I, run, ⟨fun q h => sL.keys q (keysI q h), fun name w hw => ?_⟩, fun name p ok => ?_, ?_⟩
  · rcases at_name name with ⟨-, hI⟩ | ⟨x, y, w', -, -, hI, k, -⟩
    · rw [hI] at hw; cases hw
    · by_cases kw : kept (.atom name, w') = Bool.true
      · simp only [kw, ite_true] at hI
        rw [hI] at hw; rw [← Option.some.inj hw]; exact (k kw).1
      · simp [kw] at hI; rw [hI] at hw; cases hw
  · rcases at_name name with ⟨hLR, hI⟩ | ⟨x, y, w, hL, hR, hI, k, d⟩
    · rcases hLR with h | h <;> simp [hI, h, dn_none]
    · by_cases kw : kept (.atom name, w) = Bool.true
      · simp only [kw, ite_true] at hI
        rw [hI, hL, hR, (k kw).2.1 p ok]
      · simp only [kw, Bool.false_eq_true, ite_false] at hI
        rw [hI, hL, hR, dn_none, (d (by simpa using kw)).1 p ok]
  · rcases at_name "list" with ⟨hLR, hI⟩ | ⟨x, y, w, hL, hR, hI, k, d⟩
    · rcases hLR with h | h <;> simp [hI, h, topL]
    · by_cases kw : kept (.atom "list", w) = Bool.true
      · simp [kw, hI, hL, hR, topL, (k kw).2.2 rfl]
      · simp [kw, hI, hL, hR, topL, (d (by simpa using kw)).2 rfl]

/-- The negation of a union of two non-empty types holds what the intersection of their negations holds. -/
theorem de_morgan_sem (δ : Nat) (ops : ElemOk E K) (dops : ElemDiff E K) (hK : K ≤ δ + 90) (L R : List (Term × Term)) (sL : Sem E L) (sR : Sem E R) (nL : L ≠ []) (nR : R ≠ []) :
    ∃ U A NL NR B, Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map L) (.map R) = .ok (.map U) ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map U) = .ok (.map A) ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map L) = .ok (.map NL) ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map R) = .ok (.map NR) ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.map NL) (.map NR) = .ok (.map B) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D (δ + 100)) (.map A) (.map B) = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D (δ + 100)) (.map B) (.map A) = .ok (.atom "true") := by
  obtain ⟨U, runU, sU, dU, tU, neU, nU⟩ := sem_union δ L R sL sR
  obtain ⟨A, runA, sA, dA, tA⟩ := sem_neg δ ops.term U sU (neU nL)
  obtain ⟨NL, runNL, sNL, dNL, tNL⟩ := sem_neg δ ops.term L sL nL
  obtain ⟨NR, runNR, sNR, dNR, tNR⟩ := sem_neg δ ops.term R sR nR
  obtain ⟨B, runB, sB, dB, tB⟩ := sem_inter δ NL NR sNL sNR
  have same : ∀ name ∈ names, ∀ p, PtOk name p →
      dn name (mapLookup A (.atom name)) p = dn name (mapLookup B (.atom name)) p := by
    intro name m p ok
    rw [dA name m p ok, dU name p ok, dB name p ok, dNL name m p ok, dNR name m p ok]
    cases dn name (mapLookup L (.atom name)) p <;> cases dn name (mapLookup R (.atom name)) p <;> rfl
  have top : topL (mapLookup A (.atom "list")) = topL (mapLookup B (.atom "list")) := by
    rw [tA, tB, tNL, tNR, nU]
  refine ⟨U, A, NL, NR, B, runU, runA, runNL, runNR, runB, sem_sub ops dops (m := δ + 100) (by omega) A B sA sB (fun name m p ok h => ?_)
    (fun h => by rw [top]; exact h), sem_sub ops dops (m := δ + 100) (by omega) B A sB sA (fun name m p ok h => ?_) (fun h => by rw [← top]; exact h)⟩
  · rw [← same name m p ok]; exact h
  · rw [same name m p ok]; exact h

/-! List types of element types decide their emptiness, whatever their lines. -/

/-- List literals whose element and tail types are `E`, including the top list literal. -/
def LLit (E : Term → Prop) (t : Term) : Prop :=
  ∃ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] ∧ E a ∧ E b

/-- Lines of BDDs: their positive and negative literals. -/
def LineOk (ok : Term → Prop) (line : Term) : Prop :=
  ∃ pos negs : List Term, line = .tuple #[Term.list pos, Term.list negs] ∧ (∀ t ∈ pos, ok t) ∧ ∀ t ∈ negs, ok t

theorem dnf_lines {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ (P : Term → Prop), (∀ t, ok t → P t) → ∀ (acc pos negs : List Term), (∀ l ∈ acc, LineOk P l) →
      (∀ t ∈ pos, P t) → (∀ t ∈ negs, P t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos)
        (Term.list negs) r = .ok (Term.list lines) ∧ ∀ l ∈ lines, LineOk P l := by
  refine Bdd.induction (P := fun ok r => ∀ (P : Term → Prop), (∀ t, ok t → P t) → ∀ (acc pos negs : List Term),
    (∀ l ∈ acc, LineOk P l) → (∀ t ∈ pos, P t) → (∀ t ∈ negs, P t) →
    ∃ lines : List Term, Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos)
      (Term.list negs) r = .ok (Term.list lines) ∧ ∀ l ∈ lines, LineOk P l) ?_ ?_ ?_ ?_ ok r wr
  · intro ok P _ acc pos negs ha hp hn
    refine ⟨.tuple #[Term.list pos, Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l m => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · exact ⟨pos, negs, rfl, hp, hn⟩
    · exact ha l m
  · intro ok P _ acc pos negs ha _ _
    exact ⟨acc, by simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»], ha⟩
  · intro ok k x y okl P hP acc pos negs ha hp hn
    refine ⟨.tuple #[Term.list (.tuple #[.integer k, x, y] :: pos), Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l m => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · refine ⟨_, negs, rfl, fun t mt => ?_, hn⟩
      rcases List.mem_cons.mp mt with rfl | mt
      · exact hP _ okl
      · exact hp t mt
    · exact ha l m
  · intro ok h lit c u d _ okl hc hu hd ic iu id P hP acc pos negs ha hp hn
    have hP' : ∀ t, Above ok lit t → P t := fun t ht => hP t ht.1
    obtain ⟨l₁, r₁, h₁⟩ := iu P hP' acc pos negs ha hp hn
    obtain ⟨l₂, r₂, h₂⟩ := ic P hP' l₁ (lit :: pos) negs h₁ (fun t m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hP _ okl
      · exact hp t m) hn
    obtain ⟨l₃, r₃, h₃⟩ := id P hP' l₂ pos (lit :: negs) h₂ hp (fun t m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hP _ okl
      · exact hn t m)
    refine ⟨l₃, ?_, h₃⟩
    simp only [Term.list] at r₁ r₂ r₃ ⊢
    simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», r₁, r₂, r₃]

@[simp] theorem orElse_bool (a b : Bool) :
    Lynx.Except.orElse (.ok (boolAtom a)) (.ok (boolAtom b)) Bool.true = .ok (boolAtom (a || b)) := by
  cases a <;> cases b <;> simp [boolAtom, Lynx.Except.orElse]

def litsFun : Term := .function "Elixir.Module.Types.Descr" "-non_empty_list_literals_intersection/2-fun-0-" 2 #[]

theorem lits_fold (ops : ElemOk E K) : ∀ (l : List Term), (∀ t ∈ l, LLit E t) → ∀ a b, E a → E b →
    ∃ a' b', E a' ∧ E b' ∧ ∀ m, K + 1 ≤ m →
      Erlang.lists.«foldl_1/3» (D m) litsFun (.tuple #[a, b]) (Term.list l) = .ok (.tuple #[a', b']) := by
  intro l
  induction l with
  | nil =>
    intro _ a b ha hb
    exact ⟨a, b, ha, hb, fun m _ => by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons t rest ih =>
    intro lits a b ha hb
    obtain ⟨k, x, y, rfl, hx, hy⟩ := lits _ List.mem_cons_self
    obtain ⟨a₁, ha₁, ra⟩ := ops.inter ha hx
    obtain ⟨b₁, hb₁, rb⟩ := ops.inter hb hy
    obtain ⟨a', b', ha', hb', run⟩ := ih (fun t m => lits t (List.mem_cons_of_mem _ m)) a₁ b₁ ha₁ hb₁
    refine ⟨a', b', ha', hb', fun m hm => ?_⟩
    obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only [litsFun, Erlang.program.«Elixir.Module.Types.Descr:-non_empty_list_literals_intersection/2-fun-0-/2».pure]
    simp only [Elixir.Module.Types.Descr.«-non_empty_list_literals_intersection/2-fun-0-/2», ra n hn, rb n hn,
      Lynx.Except.ok_bind, pure_bind]
    exact run (n + 1) hm

/-- `non_empty_list_literals_intersection/2` intersects the positive literals of a line. -/
theorem literals_total (ops : ElemOk E K) (S : List (Term × Term)) (pos : List Term) (lits : ∀ t ∈ pos, LLit E t) :
    (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m) (Term.list pos)
      (.map S) = .ok (.atom "empty")) ∨
    ∃ a b, E a ∧ E b ∧ ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m)
      (Term.list pos) (.map S) = .ok (.tuple #[a, b]) := by
  obtain ⟨a, b, ha, hb, fold⟩ := lits_fold ops pos lits _ _ ops.term ops.term
  obtain ⟨ea, hea⟩ := ops.empty ha S
  obtain ⟨eb, heb⟩ := ops.empty hb S
  have foldEq : ∀ d, Erlang.lists.«foldl/3» d litsFun (.tuple #[.atom "term", .atom "term"]) (Term.list pos) =
      Erlang.lists.«foldl_1/3» d litsFun (.tuple #[.atom "term", .atom "term"]) (Term.list pos) := by
    intro d
    cases pos with
    | nil =>
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», litsFun]
    | cons t rest =>
      conv => rhs; rw [Erlang.lists.«foldl_1/3».eq_def]
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», litsFun]
  have unfold : ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m)
      (Term.list pos) (.map S) = if ea || eb then .ok (.atom "empty") else .ok (.tuple #[a, b]) := by
    intro m hm
    have f := fold m hm
    have e₁ := hea m (by omega)
    have e₂ := heb m (by omega)
    unfold Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2»
    have f' : Erlang.lists.«foldl/3» (D m) (.function "Elixir.Module.Types.Descr"
        "-non_empty_list_literals_intersection/2-fun-0-" 2 #[]) (.tuple #[.atom "term", .atom "term"])
        (Term.list pos) = .ok (.tuple #[a, b]) := by rw [← litsFun, foldEq, f]
    simp only [pure_bind, f', Lynx.Except.ok_bind, e₁, e₂, orElse_bool]
    cases ea <;> cases eb <;> simp [boolAtom, isMember]
  by_cases e : (ea || eb) = Bool.true
  · exact Or.inl fun m hm => by rw [unfold m hm, ite_eq_left e]
  · exact Or.inr ⟨a, b, ha, hb, fun m hm => by rw [unfold m hm, ite_eq_right e]⟩

/-- Types whose list part `list_tail_unfold/1` removes stay element types. -/
def TailOk (E : Term → Prop) : Prop :=
  ∀ e, E e → ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧ E e'

/-- Negated list literals remove what they cover of the tail of a line. -/
theorem negs_total (ops : ElemOk E K) (dops : ElemDiff E K) (tail : TailOk E) (S : List (Term × Term))
    {list : Term} (hlist : E list) :
    ∀ negs : List Term, (∀ t ∈ negs, LLit E t) → ∀ last, E last →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list negs) list last
        (.map S)) := by
  have pos := ops.pos
  intro negs
  induction negs with
  | nil =>
    intro _ last _
    exact ⟨Bool.false, fun m _ => by
      dsimp only
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp [boolAtom]⟩
  | cons N rest ih =>
    intro lits last hlast
    obtain ⟨k, nt, nl, rfl, hnt, hnl⟩ := lits _ List.mem_cons_self
    have ih' := ih fun t m => lits t (List.mem_cons_of_mem _ m)
    obtain ⟨sd, hsd, rsd⟩ := dops.diff hlist hnt
    obtain ⟨bs, hbs⟩ := ops.empty hsd S
    cases bs
    · obtain ⟨b, hb⟩ := ih' last hlast
      refine ⟨b, fun m hm => ?_⟩
      have h₁ := hb m hm
      dsimp only at h₁ ⊢
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m (by omega), hbs m (by omega), boolAtom,
        isMember] at h₁ ⊢
      exact h₁
    · obtain ⟨t, ht, ht'⟩ := tail nl hnl
      obtain ⟨dd, hdd, rdd⟩ := dops.diff hlast ht'
      obtain ⟨be, hbe⟩ := ops.empty hdd S
      obtain ⟨b, hb⟩ := ih' dd hdd
      refine ⟨be || b, fun m hm => ?_⟩
      have h₁ := hb m hm
      have h₂ := hbe m (by omega)
      dsimp only at h₁ ⊢
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp only [] at h₁ ⊢
      simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m (by omega), hbs m (by omega), boolAtom,
        isMember, ht m (by omega), rdd m (by omega)]
      rw [h₂, h₁, orElse_bool]
      cases be <;> cases b <;> rfl

theorem line_list_total (ops : ElemOk E K) (dops : ElemDiff E K) (tail : TailOk E) (S : List (Term × Term))
    {list last : Term} (hlist : E list) (hlast : E last) {negs : List Term} (lits : ∀ t ∈ negs, LLit E t) :
    BoolAt K (fun m => Elixir.Module.Types.Descr.«list_line_empty?/4» (D m) list last (Term.list negs)
      (.map S)) := by
  have pos := ops.pos
  obtain ⟨t, ht, ht'⟩ := tail last hlast
  obtain ⟨b₁, h₁⟩ := ops.empty hlist S
  obtain ⟨b₂, h₂⟩ := ops.empty ht' S
  obtain ⟨b₃, h₃⟩ := negs_total ops dops tail S hlist negs lits t ht'
  refine ⟨b₁ || b₂ || b₃, fun m hm => ?_⟩
  have e₃ := h₃ m hm
  dsimp only at e₃ ⊢
  unfold Elixir.Module.Types.Descr.«list_line_empty?/4»
  simp only [ht m (by omega), Lynx.Except.ok_bind, h₁ m (by omega), h₂ m (by omega), e₃, orElse_bool]

/-- List types of element types decide their emptiness at every call depth from `K + 2`. -/
theorem list_total (ops : ElemOk E K) (dops : ElemDiff E K) (tail : TailOk E) (S : List (Term × Term)) {w : Term}
    (wl : Bdd (LLit E) w) :
    BoolAt (K + 2) (fun m => Elixir.Module.Types.Descr.«list_empty?/2» (D m) w (.map S)) := by
  by_cases top : w = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    exact ⟨Bool.false, fun m _ => by dsimp only; unfold Elixir.Module.Types.Descr.«list_empty?/2»; rfl⟩
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "list") w) e.1) (.cons (.atom "list") w) e.1 == .eq) = Bool.true
  · refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    unfold Elixir.Module.Types.Descr.«list_empty?/2»
    split
    · exact absurd rfl top
    · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true,
        boolAtom]
  have fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "list") w) e.1) (.cons (.atom "list") w) e.1 == .eq) = Bool.false := by
    simpa using seen
  obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "list") w) (.atom "true") (.map S) =
      .ok (.map S') := by
    simp [Erlang.maps.«put/3»]
  obtain ⟨lines, dnf, hlines⟩ := dnf_lines wl (LLit E) (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  have each : ∀ x ∈ lines, ∃ b, ∀ m', K + 1 ≤ m' →
      Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D m') (.map S') x = .ok (boolAtom b) := by
    intro x mx
    obtain ⟨pos, negs, rfl, hp, hn⟩ := hlines x mx
    rcases literals_total ops S' pos hp with empty | ⟨a, b, ha, hb, run⟩
    · exact ⟨Bool.true, fun m' h => by
        simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», empty m' h, boolAtom]⟩
    · obtain ⟨bl, hbl⟩ := line_list_total ops dops tail S' ha hb hn
      exact ⟨bl, fun m' h => by
        have := hbl m' (by omega)
        dsimp only at this
        simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», run m' h, this]⟩
  classical
  let res : Term → Bool := fun x => if h : x ∈ lines then Classical.choose (each x h) else Bool.false
  have hres : ∀ x ∈ lines, ∀ m', K + 1 ≤ m' →
      Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D m') (.map S') x = .ok (boolAtom (res x)) := by
    intro x mx m' h
    simp only [res, dite_eq_left mx]
    exact Classical.choose_spec (each x mx) m' h
  refine ⟨lines.all res, fun m hm => ?_⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
  have all := all_list (D (n + 1)) _ _ _ res lines fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-list_empty?/2-fun-0-/1».pure]
    exact hres x mx n hn
  dsimp only
  unfold Elixir.Module.Types.Descr.«list_empty?/2»
  split
  · exact absurd rfl top
  · simp only [Term.list] at dnf
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put, Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf]
    exact all

/-! Function types of element types decide their emptiness, whatever their lines. -/

@[simp] theorem boolAtom_true : boolAtom Bool.true = .atom "true" := rfl
@[simp] theorem boolAtom_false : boolAtom Bool.false = .atom "false" := rfl

theorem foldl1_uni (K : Nat) (f : Term) (Inv : Term → Prop) :
    ∀ l : List Term, (∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ ∀ m, K ≤ m → (D m).pure f #[x, a] = .ok a') →
      ∀ acc, Inv acc → ∃ r, Inv r ∧ ∀ m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list l) = .ok r := by
  intro l
  induction l with
  | nil => exact fun _ acc h => ⟨acc, h, fun m _ => by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro step acc hacc
    obtain ⟨a', ha', run⟩ := step x List.mem_cons_self acc hacc
    obtain ⟨r, hr, rest⟩ := ih (fun y my => step y (List.mem_cons_of_mem _ my)) a' ha'
    refine ⟨r, hr, fun m hm => ?_⟩
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only [run m hm, Lynx.Except.ok_bind]
    exact rest m hm

/-- Folds whose steps give the same results at every call depth from `K`. -/
theorem foldl_uni (K : Nat) (mo nm : String) (caps : Array Term) (Inv : Term → Prop) (l : List Term)
    (step : ∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ ∀ m, K ≤ m →
      (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (hacc : Inv acc) :
    ∃ r, Inv r ∧ ∀ m, K ≤ m →
      Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldl1_uni K _ Inv l step acc hacc
  refine ⟨r, hr, fun m hm => ?_⟩
  have := run m hm
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using this
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem any_uni (K : Nat) (mo nm : String) (caps : Array Term) (l : List Term)
    (each : ∀ x ∈ l, BoolAt K (fun m => (D m).pure (.function mo nm 1 caps) #[x])) :
    BoolAt K (fun m => Erlang.lists.«any/2» (D m) (.function mo nm 1 caps) (Term.list l)) := by
  classical
  let res : Term → Bool := fun x => if h : x ∈ l then Classical.choose (each x h) else Bool.false
  refine ⟨l.any res, fun m hm => any_list (D m) mo nm caps res l fun x mx => ?_⟩
  simp only [res, dite_eq_left mx]
  exact Classical.choose_spec (each x mx) m hm

theorem all_uni (K : Nat) (mo nm : String) (caps : Array Term) (l : List Term)
    (each : ∀ x ∈ l, BoolAt K (fun m => (D m).pure (.function mo nm 1 caps) #[x])) :
    BoolAt K (fun m => Erlang.lists.«all/2» (D m) (.function mo nm 1 caps) (Term.list l)) := by
  classical
  let res : Term → Bool := fun x => if h : x ∈ l then Classical.choose (each x h) else Bool.false
  refine ⟨l.all res, fun m hm => all_list (D m) mo nm caps res l fun x mx => ?_⟩
  simp only [res, dite_eq_left mx]
  exact Classical.choose_spec (each x mx) m hm

theorem map1_list (d : Dispatcher) (f : Term) (g : Term → Term) :
    ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (g x)) →
      Erlang.lists.«map_1/2» d f (Term.list l) = .ok (Term.list (l.map g)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«map_1/2», Term.list]
  | cons x xs ih =>
    intro hf
    rw [Erlang.lists.«map_1/2».eq_def]
    simp [Term.list, hf x List.mem_cons_self, ih fun y m => hf y (List.mem_cons_of_mem _ m)]

theorem map_list (d : Dispatcher) (mo nm : String) (caps : Array Term) (g : Term → Term) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function mo nm 1 caps) #[x] = .ok (g x)) :
    Erlang.lists.«map/2» d (.function mo nm 1 caps) (Term.list l) = .ok (Term.list (l.map g)) := by
  cases l with
  | nil => simp [Erlang.lists.«map/2», Erlang.erlang.«is_function/2», Term.list]
  | cons x xs =>
    have := map1_list d _ g xs fun y m => hf y (List.mem_cons_of_mem _ m)
    simp [Erlang.lists.«map/2», Erlang.erlang.«is_function/2», Term.list,
      hf x List.mem_cons_self, this]

theorem nth1_list (l : List Term) : ∀ (i : Nat), i < l.length →
    Erlang.lists.«nth_1/2» (.integer (i + 1)) (Term.list l) = .ok (l[i]?.getD .nil) := by
  induction l with
  | nil => intro i h; simp at h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp [Term.list, Erlang.lists.«nth_1/2»]
    | succ i =>
      have rest := ih i (by have h' : i + 1 < xs.length + 1 := h; omega)
      have sub : Erlang.erlang.«-/2» (.integer ((i + 1 + 1 : Nat) : Int)) (.integer 1) =
          .ok (.integer ((i + 1 : Nat) : Int)) := by
        rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
      rw [Erlang.lists.«nth_1/2».eq_def]
      simp only [Term.list] at rest ⊢
      split
      · simp_all <;> omega
      · simp_all
      · simp_all

theorem nth_list (l : List Term) (i : Nat) (h : i < l.length) :
    Erlang.lists.«nth/2» (.integer (i + 1)) (Term.list l) = .ok (l[i]?.getD .nil) := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    cases i with
    | zero => simp [Erlang.lists.«nth/2», Term.list]
    | succ i =>
      have := nth1_list (x :: xs) (i + 1) h
      unfold Erlang.lists.«nth/2»
      simp only [Term.list] at this ⊢
      split
      · simp_all <;> omega
      · have gt : compare ((i : Int) + 1 + 1) 1 = .gt := Int.compare_eq_gt.mpr (by omega)
        simp [Erlang.erlang.«>/2», Erlang.erlang.«and/2», gt]
        simpa using this

theorem replace1_list (l : List Term) : ∀ (i : Nat) (v : Term), i < l.length →
    Elixir.List.«do_replace_at/3» (Term.list l) (.integer i) v = .ok (Term.list (l.set i v)) := by
  induction l with
  | nil => intro i v h; simp at h
  | cons x xs ih =>
    intro i v h
    cases i with
    | zero => simp [Term.list, Elixir.List.«do_replace_at/3»]
    | succ i =>
      have rest := ih i v (by have h' : i + 1 < xs.length + 1 := h; omega)
      have sub : Erlang.erlang.«-/2» (.integer ((i + 1 : Nat) : Int)) (.integer 1) = .ok (.integer (i : Int)) := by
        rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
      rw [Elixir.List.«do_replace_at/3».eq_def]
      simp only [Term.list] at rest ⊢
      simp [rest, Term.list]

theorem replace_list (l : List Term) (i : Nat) (v : Term) (h : i < l.length) :
    Elixir.List.«replace_at/3» (Term.list l) (.integer i) v = .ok (Term.list (l.set i v)) := by
  have := replace1_list l i v h
  unfold Elixir.List.«replace_at/3»
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp [Erlang.erlang.«is_list/1», Erlang.erlang.«is_integer/1», Lynx.Except.andAlso,
      Erlang.erlang.«</2», this, Term.list]
    have nlt : compare (i : Int) 0 ≠ .lt := fun e => by have := Int.compare_eq_lt.mp e; omega
    simp [nlt]

/-- Recursive nodes: a reference, the state map of the equations, and the generator. -/
def IsNode (e : Term) : Prop := ∃ (r : List Nat) (st : List (Term × Term)) (g : Term), e = .tuple #[.reference r, .map st, g]

/-- Static types: the top type, maps without a dynamic part, or recursive nodes. -/
def Static (e : Term) : Prop :=
  e = .atom "term" ∨ (∃ X, e = .map X ∧ mapLookup X (.atom "dynamic") = Option.none) ∨ IsNode e

theorem split_static {e : Term} (h : Static e) :
    Elixir.Module.Types.Descr.«split_dynamic/1» e = .ok (.tuple #[e, e, .atom "false"]) := by
  rcases h with rfl | ⟨X, rfl, sX⟩ | ⟨r, st, g, rfl⟩
  · rfl
  · unfold Elixir.Module.Types.Descr.«split_dynamic/1»
    simp [getMapKeys_single, sX]
  · rfl

theorem descr_fields (l : List Term) (hl : ∀ e ∈ l, Static e) :
    ∀ (acc dacc : List Term) (se : Bool), ∃ se' : Bool,
      Elixir.Module.Types.Descr.«tuple_descr_fields/5» (Term.list l) (Term.list acc) (Term.list dacc)
        (.atom "false") (boolAtom se) =
      .ok (Term.tuple #[Term.list (l.reverse ++ acc), Term.list (l.reverse ++ dacc), Term.atom "false", boolAtom se']) := by
  induction l with
  | nil => intro acc dacc se; exact ⟨se, by simp [Elixir.Module.Types.Descr.«tuple_descr_fields/5»]⟩
  | cons x xs ih =>
    intro acc dacc se
    have hx := hl x List.mem_cons_self
    obtain ⟨se', run⟩ := ih (fun e m => hl e (List.mem_cons_of_mem _ m)) (x :: acc) (x :: dacc)
      (se || (Term.compare (Term.fuel x (.map [])) x (.map []) == .eq))
    refine ⟨se', ?_⟩
    have eq : Erlang.erlang.«==/2» x (.map []) = .ok (boolAtom (Term.compare (Term.fuel x (.map [])) x (.map []) == .eq)) := by
      simp only [Erlang.erlang.«==/2»]; cases h : Term.compare (Term.fuel x (.map [])) x (.map []) <;> simp [boolAtom]
    rw [Elixir.Module.Types.Descr.«tuple_descr_fields/5».eq_def]
    simp only [Term.list] at run ⊢
    cases se <;> cases hd : (Term.compare (Term.fuel x (.map [])) x (.map []) == .eq) <;>
      simp_all [split_static hx, Lynx.Except.orElse, boolAtom]

theorem bsl27 (x : Int) : Erlang.erlang.«bsl/2» (.integer x) (.integer 27) = .ok (.integer (x <<< (27 : Nat))) := rfl

theorem leaf_closed (l : List Term) : ∃ k : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list l) =
      .ok (.tuple #[.integer k, .atom "closed", Term.list l]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (Term.list l)
  have len := length_list l
  obtain ⟨v, key⟩ : ∃ v : Int, Elixir.Module.Types.Descr.«bdd_leaf_key/2» (Term.list l) (.integer hash) =
      .ok (.integer v) := by
    unfold Elixir.Module.Types.Descr.«bdd_leaf_key/2»
    cases l <;> simp only [Term.list] at len ⊢ <;>
      simp [Erlang.erlang.«is_list/1», len, bsl27]
  simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, key, Erlang.erlang.«-/2_integers»]

theorem reverse2_list (l : List Term) : ∀ acc : List Term,
    Erlang.lists.«reverse/2» (Term.list l) (Term.list acc) = .ok (Term.list (l.reverse ++ acc)) := by
  induction l with
  | nil => intro acc; simp [Erlang.lists.«reverse/2»]
  | cons x xs ih => intro acc; simpa [Term.list, Erlang.lists.«reverse/2»] using ih (x :: acc)

theorem reverse1_list (l : List Term) : Erlang.lists.«reverse/1» (Term.list l) = .ok (Term.list l.reverse) := by
  match l with
  | [] => rfl
  | [a] => rfl
  | [a, b] => rfl
  | a :: b :: c :: rest =>
    have := reverse2_list (c :: rest) [b, a]
    simp only [Term.list] at this ⊢
    simp [Erlang.lists.«reverse/1», this, Term.list]

theorem leaf_fun (args : List Term) : ∃ k : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (Term.list args) (.atom "term") =
      .ok (.tuple #[.integer k, Term.list args, .atom "term"]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (Term.list args) (.atom "term"))
  unfold Elixir.Module.Types.Descr.«bdd_leaf_new/2»
  cases args <;> simp [hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2»,
    Erlang.erlang.«is_list/1», Term.list]

/-- The domain of arguments: the closed tuple of them. -/
theorem args_domain (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", Term.list l])]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf⟩ := leaf_closed l
  refine ⟨k, ?_⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  unfold Elixir.Module.Types.Descr.«args_to_domain/1»
  cases l <;> simp_all [Erlang.erlang.«is_list/1», Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2», Term.list]

/-- Element types that also unite into element types, decide subtyping and disjointness, and are static,
with the same results at every call depth from `K`. -/
structure ElemFun (E : Term → Prop) (K : Nat) : Prop where
  static : ∀ {a}, E a → Static a
  union : ∀ {a b}, E a → E b → ∃ c, E c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c
  sub : ∀ {a b}, E a → E b → BoolAt K (fun m => Elixir.Module.Types.Descr.«subtype?/2» (D m) a b)
  disj : ∀ {a b}, E a → E b → BoolAt K (fun m => Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b)

/-- Domains of function types: maps holding the domains of arguments `E`, closed under unions,
intersections, and differences, whose emptiness is decided, at every call depth from `K`. -/
structure DomOk (Dm E : Term → Prop) (K : Nat) : Prop where
  dom : ∀ l : List Term, (∀ a ∈ l, E a) → ∃ t, Dm t ∧ Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) = .ok t
  none : Dm (.map [])
  isMap : ∀ {a}, Dm a → ∃ X, a = .map X
  union : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c
  inter : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c
  diff : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c
  empty : ∀ {a}, Dm a → ∀ S : List (Term × Term), ∃ b : Bool, ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)

/-- Arguments of `phi/5`: pairs of a flag and an element type. -/
def PhiArgs (E : Term → Prop) (args : List Term) : Prop :=
  ∀ a ∈ args, ∃ (b : Bool) (t : Term), a = .tuple #[boolAtom b, t] ∧ E t

/-- Caches of `phi/5`: maps to Booleans. -/
def PhiCache (C : List (Term × Term)) : Prop := ∀ q v, mapLookup C q = some v → ∃ b : Bool, v = boolAtom b

theorem PhiCache.put {C : List (Term × Term)} (hC : PhiCache C) (k : Term) (b : Bool) :
    PhiCache ((k, boolAtom b) :: C) := by
  intro q v h
  by_cases e : compareExact (fuel q k) q k = .eq
  · simp [mapLookup, e] at h
    exact ⟨b, h.symm⟩
  · exact hC q v (by simpa [mapLookup, List.find?_cons, e] using h)

theorem phi_nil (ops : ElemOk E K) (S : List (Term × Term)) (args : List Term) (hargs : PhiArgs E args)
    (b : Bool) {t : Term} (ht : E t) (C : List (Term × Term)) (hC : PhiCache C) :
    ∃ (r : Bool) (C' : List (Term × Term)), PhiCache C' ∧ ∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«phi/5» (D m) (Term.list args) (.tuple #[boolAtom b, t]) .nil (.map C) (.map S) =
        .ok (.tuple #[boolAtom r, .map C']) := by
  obtain ⟨ab, hab⟩ := any_uni (K + 1) "Elixir.Module.Types.Descr" "-phi/5-fun-0-" #[.map S] args (fun a ma => by
    obtain ⟨b', t', rfl, ht'⟩ := hargs a ma
    obtain ⟨e, he⟩ := ops.empty ht' S
    refine ⟨b' && e, fun m hm => ?_⟩
    obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    dsimp only
    rw [Erlang.program.«Elixir.Module.Types.Descr:-phi/5-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-phi/5-fun-0-/2», he n hn]
    cases b' <;> cases e <;> rfl)
  obtain ⟨e, he⟩ := ops.empty ht S
  refine ⟨ab || (b && e), _, hC.put (.tuple #[Term.list args, .tuple #[boolAtom b, t], .nil]) (ab || (b && e)),
    fun m hm => ?_⟩
  have h₁ := hab m hm
  dsimp only at h₁
  unfold Elixir.Module.Types.Descr.«phi/5»
  simp only [h₁, he m (by omega), pure_bind]
  cases ab <;> cases b <;> cases e <;> rfl

theorem PhiArgs.set {args : List Term} (h : PhiArgs E args) (i : Nat) (b : Bool) {t : Term} (ht : E t) :
    PhiArgs E (args.set i (.tuple #[boolAtom b, t])) := by
  intro a ma
  rcases List.mem_or_eq_of_mem_set ma with ma | rfl
  · exact h a ma
  · exact ⟨b, t, rfl, ht⟩

/-- `phi_arguments/7` returns a Boolean and a cache of Booleans, at every call depth from `K + 1`,
when `phi/5` does for the remaining positive literals. -/
theorem phi_args_total (ops : ElemOk E K) (dops : ElemDiff E K) (n : Int) (S : List (Term × Term))
    (rest : List Term)
    (phi : ∀ args, PhiArgs E args → (args.length : Int) = n → ∀ (b : Bool) t, E t → ∀ C, PhiCache C →
      ∃ (r : Bool) (C' : List (Term × Term)), PhiCache C' ∧ ∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«phi/5» (D m) (Term.list args) (.tuple #[boolAtom b, t]) (Term.list rest)
          (.map C) (.map S) = .ok (.tuple #[boolAtom r, .map C'])) :
    ∀ (types : List Term) (i : Nat) (args : List Term), PhiArgs E args → (args.length : Int) = n →
      (∀ x ∈ types, E x) → i + types.length = args.length → ∀ (b : Bool) t, E t → ∀ C, PhiCache C →
      ∃ (r : Bool) (C' : List (Term × Term)), PhiCache C' ∧ ∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«phi_arguments/7» (D m) (Term.list types) (.integer i) (Term.list args)
          (.tuple #[boolAtom b, t]) (Term.list rest) (.map C) (.map S) = .ok (.tuple #[boolAtom r, .map C']) := by
  intro types
  induction types with
  | nil =>
    intro i args _ _ _ _ b t _ C hC
    exact ⟨Bool.true, C, hC, fun m _ => by
      unfold Elixir.Module.Types.Descr.«phi_arguments/7»; simp [boolAtom]⟩
  | cons ty tys ih =>
    intro i args hargs hlen htys hi b t ht C hC
    have hty := htys ty List.mem_cons_self
    have htys' : ∀ x ∈ tys, E x := fun x m => htys x (List.mem_cons_of_mem _ m)
    have lt : i < args.length := by simp at hi; omega
    obtain ⟨b', a, ha, hEa⟩ := hargs _ (List.getElem_mem lt)
    have nth : Erlang.lists.«nth/2» (.integer ((i : Int) + 1)) (Term.list args) = .ok (.tuple #[boolAtom b', a]) := by
      have := nth_list args i lt
      simp only [List.getElem?_eq_getElem lt, Option.getD_some, ha] at this
      simpa using this
    have plus : Erlang.erlang.«+/2» (.integer (i : Int)) (.integer 1) = .ok (.integer ((i : Int) + 1)) := by
      simp
    obtain ⟨d, hd, rd⟩ := dops.diff hEa hty
    obtain ⟨ed, hed⟩ := ops.empty hd S
    have next := fun C' hC' => ih (i + 1) args hargs hlen htys' (by simp at hi ⊢; omega) b t ht C' hC'
    cases ed
    · have set := replace_list args i (.tuple #[Term.atom "true", d]) lt
      obtain ⟨r₁, C₁, hC₁, run₁⟩ := phi (args.set i (.tuple #[boolAtom Bool.true, d])) (hargs.set i Bool.true hd)
        (by simpa using hlen) b t ht C hC
      cases r₁
      · refine ⟨Bool.false, C₁, hC₁, fun m hm => ?_⟩
        have run₁' := run₁ m hm
        unfold Elixir.Module.Types.Descr.«phi_arguments/7»
        simp only [boolAtom_true, boolAtom_false] at nth set run₁' ⊢
        simp [nth, rd m (by omega), hed m (by omega), isMember, set, run₁']
      · obtain ⟨r, C', hC', run⟩ := next C₁ hC₁
        refine ⟨r, C', hC', fun m hm => ?_⟩
        have run' := run m hm
        have run₁' := run₁ m hm
        unfold Elixir.Module.Types.Descr.«phi_arguments/7»
        simp only [boolAtom_true] at nth set run₁' run' ⊢
        simp [nth, rd m (by omega), hed m (by omega), isMember, set, run₁']
        simpa [plus] using run'
    · obtain ⟨r, C', hC', run⟩ := next C hC
      refine ⟨r, C', hC', fun m hm => ?_⟩
      have run' := run m hm
      unfold Elixir.Module.Types.Descr.«phi_arguments/7»
      simp only [] at nth run' ⊢
      simp [nth, rd m (by omega), hed m (by omega), boolAtom_true, isMember]
      simpa [plus] using run'

/-- `phi/5` returns a Boolean and a cache of Booleans at every call depth from `K + 1`. -/
theorem phi_total (ops : ElemOk E K) (dops : ElemDiff E K) (n : Int) (S : List (Term × Term)) :
    ∀ (pos : List Term), (∀ t ∈ pos, FunLit E n t) → ∀ args, PhiArgs E args → (args.length : Int) = n →
      ∀ (b : Bool) t, E t → ∀ C, PhiCache C →
      ∃ (r : Bool) (C' : List (Term × Term)), PhiCache C' ∧ ∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«phi/5» (D m) (Term.list args) (.tuple #[boolAtom b, t]) (Term.list pos)
          (.map C) (.map S) = .ok (.tuple #[boolAtom r, .map C']) := by
  intro pos
  induction pos with
  | nil => intro _ args hargs _ b t ht C hC; exact phi_nil ops S args hargs b ht C hC
  | cons p rest ih =>
    intro hpos args hargs hlen b ret hret C hC
    obtain ⟨k, arguments, ret', rfl, alen, harguments, hret'⟩ := hpos p List.mem_cons_self
    have ih' := ih fun t m => hpos t (List.mem_cons_of_mem _ m)
    let key := Term.tuple #[Term.list args, .tuple #[boolAtom b, ret],
      Term.list (.tuple #[.integer k, Term.list arguments, ret'] :: rest)]
    cases hk : mapLookup C key with
    | some v =>
      obtain ⟨r, rfl⟩ := hC _ _ hk
      refine ⟨r, C, hC, fun m _ => ?_⟩
      unfold Elixir.Module.Types.Descr.«phi/5»
      simp only [key, Term.list] at hk ⊢
      simp only [getMapKeys_single, pure_bind, hk, Option.toList]
      rfl
    | none =>
      obtain ⟨meet, hmeet, rmeet⟩ := ops.inter hret hret'
      obtain ⟨em, hem⟩ := ops.empty hmeet S
      have args0 := phi_args_total ops dops n S rest ih' arguments 0 args hargs hlen harguments
        (by simp; omega) b ret hret
      cases em
      · obtain ⟨r₁, C₁, hC₁, run₁⟩ := ih' args hargs hlen Bool.true meet hmeet C hC
        cases r₁
        · refine ⟨Bool.false, _, hC₁.put key Bool.false, fun m hm => ?_⟩
          have run₁' := run₁ m hm
          unfold Elixir.Module.Types.Descr.«phi/5»
          simp only [key, Term.list, boolAtom_true, boolAtom_false] at hk run₁' ⊢
          simp only [getMapKeys_single, pure_bind, hk, Option.toList]
          simp [ rmeet m (by omega), hem m (by omega), boolAtom_false, isMember,
            run₁', Erlang.maps.«put/3»]
        · obtain ⟨r, C', hC', run⟩ := args0 C₁ hC₁
          refine ⟨r, _, hC'.put key r, fun m hm => ?_⟩
          have run₁' := run₁ m hm
          have run' := run m hm
          unfold Elixir.Module.Types.Descr.«phi/5»
          simp only [key, Term.list, boolAtom_true, Int.natCast_zero] at hk run₁' run' ⊢
          simp only [getMapKeys_single, pure_bind, hk, Option.toList]
          simp [ rmeet m (by omega), hem m (by omega), boolAtom_false, isMember,
            run₁', run', Erlang.maps.«put/3»]
      · obtain ⟨r, C', hC', run⟩ := args0 C hC
        refine ⟨r, _, hC'.put key r, fun m hm => ?_⟩
        have run' := run m hm
        unfold Elixir.Module.Types.Descr.«phi/5»
        simp only [key, Term.list, Int.natCast_zero] at hk run' ⊢
        simp only [getMapKeys_single, pure_bind, hk, Option.toList]
        simp [ rmeet m (by omega), hem m (by omega), boolAtom_true, isMember,
          run', Erlang.maps.«put/3»]

theorem aux_apply_total (ops : ElemOk E K) (fops : ElemFun E K) (dm : DomOk Dm E K) (n : Int) :
    ∀ arrows : List Term, (∀ t ∈ arrows, FunLit E n t) → ∀ result input rets, E result → Dm input → E rets →
      ∃ r, E r ∧ ∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«aux_apply/4» (D m) result input rets (Term.list arrows) = .ok r := by
  intro arrows
  induction arrows with
  | nil =>
    intro _ result input rets hres _ hrets
    obtain ⟨sb, hsb⟩ := fops.sub hrets hres
    obtain ⟨u, hu, ru⟩ := fops.union hres hrets
    cases sb
    · exact ⟨u, hu, fun m hm => by
        have h := hsb m hm; dsimp only at h
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [h, isMember, ru m hm]⟩
    · exact ⟨result, hres, fun m hm => by
        have h := hsb m hm; dsimp only at h
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [h, isMember]⟩
  | cons p rest ih =>
    intro harrows result input rets hres hin hrets
    obtain ⟨k, args, ret, rfl, -, hargs, hret⟩ := harrows p List.mem_cons_self
    have ih' := ih fun t m => harrows t (List.mem_cons_of_mem _ m)
    obtain ⟨dom, hdom, rdom⟩ := dm.dom args hargs
    obtain ⟨sub, hsub, rsub⟩ := dm.diff hin hdom
    obtain ⟨refine, hrefine, rrefine⟩ := ops.inter hrets hret
    obtain ⟨X, rfl⟩ := dm.isMap hsub
    obtain ⟨es, hes⟩ := dm.empty hsub []
    cases es
    · obtain ⟨r₁, hr₁, run₁⟩ := ih' result (.map X) rets hres hsub hrets
      obtain ⟨r, hr, run⟩ := ih' r₁ input refine hr₁ hin hrefine
      exact ⟨r, hr, fun m hm => by
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [rdom, rsub m hm, rrefine m hm, Elixir.Module.Types.Descr.«empty?/1», hes m hm,
          isMember]
        simp [run₁ m hm, run m hm]⟩
    · obtain ⟨r, hr, run⟩ := ih' result input refine hres hin hrefine
      exact ⟨r, hr, fun m hm => by
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [rdom, rsub m hm, rrefine m hm, Elixir.Module.Types.Descr.«empty?/1», hes m hm,
          isMember]
        simp [run m hm]⟩

theorem apply_static_total (ops : ElemOk E K) (fops : ElemFun E K) (dm : DomOk Dm E K) (hnone : E (.map []))
    (n : Int) (args : List Term) (hargs : ∀ a ∈ args, E a) (pos : List Term) (hpos : ∀ t ∈ pos, FunLit E n t) :
    ∃ r, E r ∧ ∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«fun_apply_static/2» (D m) (Term.list args) (Term.list [Term.list pos]) = .ok r := by
  obtain ⟨dom, hdom, rdom⟩ := dm.dom args hargs
  obtain ⟨r, hr, run⟩ := foldl_uni (K + 1) "Elixir.Module.Types.Descr" "-fun_apply_static/2-fun-0-" #[dom] E
    [Term.list pos] (by
      intro x mx a ha
      rw [List.mem_singleton.mp mx]
      obtain ⟨r, hr, run⟩ := aux_apply_total ops fops dm n pos hpos a dom (.atom "term") ha hdom ops.term
      refine ⟨r, hr, fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_static/2-fun-0-/2».pure]
      exact run m' hm') (.map []) hnone
  exact ⟨r, hr, fun m hm => by
    unfold Elixir.Module.Types.Descr.«fun_apply_static/2»
    simp [rdom, run m hm]⟩

theorem apply_disjoint_total (fops : ElemFun E K) (dm : DomOk Dm E K) (hnone : E (.map []))
    (n : Int) (args : List Term) (hargs : ∀ a ∈ args, E a) (pos : List Term) (hpos : ∀ t ∈ pos, FunLit E n t) :
    ∃ r, E r ∧ ∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«apply_disjoint/2» (D m) (Term.list args) (Term.list pos) = .ok r := by
  obtain ⟨dom, hdom, rdom⟩ := dm.dom args hargs
  obtain ⟨r, hr, run⟩ := foldl_uni (K + 1) "Elixir.Module.Types.Descr" "-apply_disjoint/2-fun-0-" #[dom] E
    pos (by
      intro x mx a ha
      obtain ⟨k, args', ret', rfl, -, hargs', hret'⟩ := hpos x mx
      obtain ⟨dom', hdom', rdom'⟩ := dm.dom args' hargs'
      obtain ⟨i, hi, ri⟩ := dm.inter hdom' hdom
      obtain ⟨X, rfl⟩ := dm.isMap hi
      obtain ⟨e, he⟩ := dm.empty hi []
      obtain ⟨u, hu, ru⟩ := fops.union ha hret'
      cases e
      · refine ⟨u, hu, fun m hm => ?_⟩
        obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm',
          Elixir.Module.Types.Descr.«empty?/1», he m' hm', isMember, ru m' hm']
      · refine ⟨a, ha, fun m hm => ?_⟩
        obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm',
          Elixir.Module.Types.Descr.«empty?/1», he m' hm', isMember]) (.map []) hnone
  exact ⟨r, hr, fun m hm => by
    unfold Elixir.Module.Types.Descr.«apply_disjoint/2»
    simp [rdom, run m hm]⟩

theorem disjoint_args_total (fops : ElemFun E K) :
    ∀ (l₁ l₂ : List Term), (∀ a ∈ l₁, E a) → (∀ a ∈ l₂, E a) → l₁.length = l₂.length →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m) (Term.list l₁) (Term.list l₂)) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ len
    cases l₂ with
    | nil => exact ⟨Bool.false, fun m _ => by
        dsimp only; unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»; simp⟩
    | cons _ _ => simp at len
  | cons a l₁ ih =>
    intro l₂ h₁ h₂ len
    cases l₂ with
    | nil => simp at len
    | cons b l₂ =>
      obtain ⟨d, hd⟩ := fops.disj (h₁ a List.mem_cons_self) (h₂ b List.mem_cons_self)
      obtain ⟨r, hr⟩ := ih l₂ (fun x m => h₁ x (List.mem_cons_of_mem _ m))
        (fun x m => h₂ x (List.mem_cons_of_mem _ m)) (by simpa using len)
      refine ⟨d || r, fun m hm => ?_⟩
      have e₁ := hd m hm
      have e₂ := hr m hm
      dsimp only at e₁ e₂ ⊢
      unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»
      rw [e₁, e₂, orElse_bool]

theorem all_disjoint_total (fops : ElemFun E K) (n : Int) :
    ∀ pos : List Term, (∀ t ∈ pos, FunLit E n t) →
      BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«all_disjoint_arguments?/1» (D m) (Term.list pos)) := by
  intro pos
  induction pos with
  | nil => intro _; exact ⟨Bool.true, fun m _ => by
      dsimp only; unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»; simp⟩
  | cons p rest ih =>
    intro hpos
    obtain ⟨k, args, ret, rfl, alen, hargs, -⟩ := hpos p List.mem_cons_self
    have hrest : ∀ t ∈ rest, FunLit E n t := fun t m => hpos t (List.mem_cons_of_mem _ m)
    have each := all_uni (K + 1) "Elixir.Module.Types.Descr" "-all_disjoint_arguments?/1-fun-0-" #[Term.list args]
      rest (fun q mq => by
        obtain ⟨k', args', ret', rfl, alen', hargs', -⟩ := hrest q mq
        obtain ⟨b, hb⟩ := disjoint_args_total fops args args' hargs hargs' (by omega)
        refine ⟨b, fun m hm => ?_⟩
        obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        dsimp only
        rw [Erlang.program.«Elixir.Module.Types.Descr:-all_disjoint_arguments?/1-fun-0-/1».pure]
        simp only [Elixir.Module.Types.Descr.«-all_disjoint_arguments?/1-fun-0-/2»]
        exact hb m' hm')
    obtain ⟨b, hb⟩ := BoolAt.andAlso each (ih hrest)
    refine ⟨b, fun m hm => ?_⟩
    have h := hb m hm
    dsimp only at h ⊢
    unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»
    simpa [Term.list] using h

theorem nonempty_args_total (ops : ElemOk E K) (S : List (Term × Term)) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (name : String) (lam : ∀ d a, (D (d + 1)).pure (.function "Elixir.Module.Types.Descr" name 1 #[.map S]) #[a] =
      (do let e ← Elixir.Module.Types.Descr.«empty_seen?/2» (D d) a (.map S); Erlang.erlang.«not/1» e)) :
    BoolAt (K + 1) (fun m => Erlang.lists.«all/2» (D m) (.function "Elixir.Module.Types.Descr" name 1 #[.map S])
      (Term.list args)) :=
  all_uni (K + 1) _ _ _ args fun a ma => by
    obtain ⟨e, he⟩ := ops.empty (hargs a ma) S
    refine ⟨!e, fun m hm => ?_⟩
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    dsimp only
    rw [lam, he m' hm']
    cases e <;> rfl

/-- `disjoint_non_empty_domains?/3` classifies the positive literals at every call depth from `K + 2`. -/
theorem domains_total (ops : ElemOk E K) (fops : ElemFun E K) (n : Int) (S : List (Term × Term))
    (args : List Term) (hargs : ∀ a ∈ args, E a) (pos : List Term) (hpos : ∀ t ∈ pos, FunLit E n t) :
    ∃ v, (v = .atom "nil" ∨ v = .atom "disjoint_non_empty" ∨ v = .atom "non_empty") ∧ ∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3» (D m) (Term.list args) (Term.list pos) (.map S) =
        .ok v := by
  obtain ⟨a₁, h₁⟩ := nonempty_args_total ops S args hargs "-disjoint_non_empty_domains?/3-fun-0-" (fun d a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-disjoint_non_empty_domains?/3-fun-0-/1».pure]; rfl)
  obtain ⟨a₂, h₂⟩ := all_uni (K + 2) "Elixir.Module.Types.Descr" "-all_non_empty_arguments?/2-fun-1-" #[.map S] pos
    (fun p mp => by
      obtain ⟨k, args', ret', rfl, -, hargs', -⟩ := hpos p mp
      obtain ⟨b, hb⟩ := nonempty_args_total ops S args' hargs' "-all_non_empty_arguments?/2-fun-0-" (fun d a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-0-/1».pure]; rfl)
      refine ⟨b, fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      dsimp only
      rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-1-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-all_non_empty_arguments?/2-fun-1-/2»]
      exact hb m' (by omega))
  obtain ⟨dj, hdj⟩ := all_disjoint_total fops n pos hpos
  refine ⟨if a₁ && a₂ then (if dj then .atom "disjoint_non_empty" else .atom "non_empty") else .atom "nil",
    by split <;> (try split) <;> simp, fun m hm => ?_⟩
  have e₁ := h₁ m (by omega)
  have e₂ := h₂ m hm
  have e₃ := hdj m (by omega)
  dsimp only at e₁ e₂ e₃
  unfold Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3»
  simp only [Elixir.Module.Types.Descr.«all_non_empty_arguments?/2», pure_bind, e₁, e₂, andAlso_bool]
  cases a₁ <;> cases a₂ <;> cases dj <;>
    simp [e₃, Lynx.Except.andAlso, Erlang.erlang.«/=/2», boolAtom]

theorem negation_total (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (hnone : E (.map []))
    {ret : Term} (hret : E ret) :
    ∃ neg, E neg ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_negation/1» (D m) ret = .ok neg := by
  rcases fops.static hret with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩
  · exact ⟨.map [], hnone, fun m _ => by unfold Elixir.Module.Types.Descr.«bare_negation/1»; rfl⟩
  all_goals
    obtain ⟨c, hc, rc⟩ := dops.diff ops.term hret
    exact ⟨c, hc, fun m hm => by unfold Elixir.Module.Types.Descr.«bare_negation/1»; exact rc m hm⟩

/-- `phi_starter/4` returns a Boolean at every call depth from `K + 2`. -/
theorem phi_starter_total (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (dm : DomOk Dm E K)
    (hnone : E (.map [])) (n : Int) (S : List (Term × Term)) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (len : (args.length : Int) = n) {ret : Term} (hret : E ret) (pos : List Term) (hpos : ∀ t ∈ pos, FunLit E n t) :
    BoolAt (K + 2) (fun m => Elixir.Module.Types.Descr.«phi_starter/4» (D m) (Term.list args) ret (Term.list pos)
      (.map S)) := by
  obtain ⟨v, hv, rv⟩ := domains_total ops fops n S args hargs pos hpos
  rcases hv with rfl | rfl | rfl
  · obtain ⟨neg, hneg, rneg⟩ := negation_total ops dops fops hnone hret
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" 1 #[])
        (Term.list args) = .ok (Term.list (args.map fun x => .tuple #[boolAtom Bool.false, x])) := fun m =>
      map_list (D m) _ _ _ _ args fun x _ => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-phi_starter/4-fun-0-/1».pure]; rfl
    obtain ⟨r, C', -, run⟩ := phi_total ops dops n S pos hpos (args.map fun x => .tuple #[boolAtom Bool.false, x])
      (fun a ma => by
        obtain ⟨x, mx, rfl⟩ := List.mem_map.mp ma
        exact ⟨Bool.false, x, rfl, hargs x mx⟩) (by simpa using len) Bool.false neg hneg [] (fun q v h => by
        simp [mapLookup] at h)
    refine ⟨r, fun m hm => ?_⟩
    have e := run m (by omega)
    simp only [boolAtom_false] at e margs
    dsimp only
    unfold Elixir.Module.Types.Descr.«phi_starter/4»
    simp [rv m hm, margs, rneg m (by omega), e]
  · obtain ⟨a, ha, ra⟩ := apply_disjoint_total fops dm hnone n args hargs pos hpos
    obtain ⟨sb, hsb⟩ := fops.sub ha hret
    refine ⟨sb, fun m hm => ?_⟩
    have e := hsb m (by omega)
    dsimp only at e ⊢
    unfold Elixir.Module.Types.Descr.«phi_starter/4»
    simp [rv m hm, ra m (by omega), e]
  · obtain ⟨a, ha, ra⟩ := apply_static_total ops fops dm hnone n args hargs pos hpos
    obtain ⟨sb, hsb⟩ := fops.sub ha hret
    refine ⟨sb, fun m hm => ?_⟩
    have e := hsb m (by omega)
    dsimp only at e ⊢
    unfold Elixir.Module.Types.Descr.«phi_starter/4»
    simp [rv m hm, ra m (by omega), e]

theorem fetch_domain_total (dm : DomOk Dm E K) (n : Int) (pos : List Term) (hpos : ∀ t ∈ pos, FunLit E n t) :
    ∃ fd, Dm fd ∧ ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«fetch_domain/1» (D m) (Term.list pos) = .ok fd := by
  obtain ⟨fd, hfd, run⟩ := foldl_uni (K + 1) "Elixir.Module.Types.Descr" "-fetch_domain/1-fun-0-" #[] Dm pos (by
    intro x mx a ha
    obtain ⟨k, args, ret, rfl, -, hargs, -⟩ := hpos x mx
    obtain ⟨dom, hdom, rdom⟩ := dm.dom args hargs
    obtain ⟨u, hu, ru⟩ := dm.union ha hdom
    refine ⟨u, hu, fun m hm => ?_⟩
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fetch_domain/1-fun-0-/2».pure]
    simp [Elixir.Module.Types.Descr.«-fetch_domain/1-fun-0-/2», rdom, ru m' hm']) (.map []) dm.none
  exact ⟨fd, hfd, fun m hm => by unfold Elixir.Module.Types.Descr.«fetch_domain/1»; exact run m hm⟩

/-- Lines with positive literals: some negative literal covers them, at every call depth from `K + 3`. -/
theorem fun_line_pos (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (dm : DomOk Dm E K)
    (hnone : E (.map [])) (n : Int) (S : List (Term × Term)) (p : Term) (rest negs : List Term)
    (hpos : ∀ t ∈ p :: rest, FunLit E n t) (hneg : ∀ t ∈ negs, FunLit E n t) :
    BoolAt (K + 3) (fun m => Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (Term.list (p :: rest))
      (Term.list negs) (.map S)) := by
  obtain ⟨fd, hfd, rfd⟩ := fetch_domain_total dm n (p :: rest) hpos
  obtain ⟨b, hb⟩ := any_uni (K + 3) "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-1-"
    #[Term.list (p :: rest), .map S] negs (fun q mq => by
      obtain ⟨k, nargs, nret, rfl, nlen, hnargs, hnret⟩ := hneg q mq
      obtain ⟨dom, hdom, rdom⟩ := dm.dom nargs hnargs
      obtain ⟨d, hd, rd⟩ := dm.diff hdom hfd
      obtain ⟨e, he⟩ := dm.empty hd S
      obtain ⟨ps, hps⟩ := phi_starter_total ops dops fops dm hnone n S nargs hnargs nlen hnret (p :: rest) hpos
      refine ⟨e && ps, fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      have e₂ := hps m' (by omega)
      dsimp only at e₂ ⊢
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-1-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3», rdom, rfd m' (by omega),
        Elixir.Module.Types.Descr.«subtype_seen?/3», rd m' (by omega), he m' (by omega), e₂, Lynx.Except.ok_bind,
        andAlso_bool])
  refine ⟨b, fun m hm => ?_⟩
  have h := hb m hm
  dsimp only at h ⊢
  rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
  simpa [Term.list] using h

/-- Lines of function literals of element types decide their emptiness at every call depth from `K + 3`. -/
theorem fun_line_total (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (dm : DomOk Dm E K)
    (hnone : E (.map [])) (n : Int) (S : List (Term × Term)) (pos negs : List Term)
    (hpos : ∀ t ∈ pos, FunLit E n t) (hneg : ∀ t ∈ negs, FunLit E n t) :
    BoolAt (K + 3) (fun m => Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (Term.list pos) (Term.list negs)
      (.map S)) := by
  cases pos with
  | cons p rest => exact fun_line_pos ops dops fops dm hnone n S p rest negs hpos hneg
  | nil =>
    cases negs with
    | nil => exact ⟨Bool.false, fun m _ => by
        dsimp only; rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]; simp⟩
    | cons q qs =>
      obtain ⟨k, args, ret, rfl, len, -, -⟩ := hneg _ List.mem_cons_self
      obtain ⟨kt, leaf⟩ := leaf_fun (args.map fun _ => .map [])
      have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-0-" 1 #[])
          (Term.list args) = .ok (Term.list (args.map fun _ => .map [])) := fun m =>
        map_list (D m) _ _ _ _ args fun x _ => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-0-/1».pure]; rfl
      obtain ⟨b, hb⟩ := fun_line_pos ops dops fops dm hnone n S
        (.tuple #[.integer kt, Term.list (args.map fun _ => .map []), .atom "term"]) [] _
        (fun t mt => by
          rw [List.mem_singleton.mp mt]
          exact ⟨kt, _, _, rfl, by simpa using len, fun a ma => by
            obtain ⟨_, _, rfl⟩ := List.mem_map.mp ma; exact hnone, ops.term⟩) hneg
      refine ⟨b, fun m hm => ?_⟩
      have h := hb m hm
      dsimp only at h ⊢
      rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
      simp only [Term.list] at h ⊢
      simp [margs, leaf, h]

/-- Function types of element types decide their emptiness at every call depth from `K + 5`. -/
theorem fun_total (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (dm : DomOk Dm E K)
    (hnone : E (.map [])) {w : Term} (fw : FField E w) (S : List (Term × Term)) :
    BoolAt (K + 5) (fun m => Elixir.Module.Types.Descr.«fun_empty?/2» (D m) w (.map S)) := by
  obtain ⟨p, R, rfl, bR⟩ := fw
  cases p
  · exact ⟨Bool.false, fun m _ => by dsimp only; unfold Elixir.Module.Types.Descr.«fun_empty?/2»; rfl⟩
  obtain ⟨b, hb⟩ := all_uni (K + 5) "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-1-" #[.map S]
    ((mapEntries R).map fun e => .tuple #[e.1, e.2]) (fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      have wv := bR _ _ (mapLookup_of_mem_mapEntries me)
      let n : Int := match e.1 with | .integer z => z | _ => 0
      have conv : ∀ t, FunArity E e.1 t → FunLit E n t := by
        rintro t ⟨z, hz, lit⟩
        simp only [n, hz]
        exact lit
      by_cases seen : S.any (fun s => Term.compareExact (Term.fuel (.cons e.1 e.2) s.1) (.cons e.1 e.2) s.1 == .eq) = Bool.true
      · refine ⟨Bool.true, fun m hm => ?_⟩
        obtain ⟨m', rfl, -⟩ := succ_of_le (show 1 ≤ m by omega)
        dsimp only
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
        simp [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2», Elixir.Module.Types.Descr.«empty_bdd_seen_key/2»,
          Erlang.erlang.«is_map_key/2», seen, Term.true]
      have fresh : S.any (fun s => Term.compareExact (Term.fuel (.cons e.1 e.2) s.1) (.cons e.1 e.2) s.1 == .eq) = Bool.false := by simpa using seen
      obtain ⟨lines, dnf, hlines⟩ := dnf_lines wv (FunLit E n) conv [] [] [] (by simp) (by simp) (by simp)
      obtain ⟨lb, hlb⟩ := all_uni (K + 4) "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-0-"
        #[.map ((.cons e.1 e.2, .atom "true") :: S)] lines (fun l ml => by
          obtain ⟨pos, negs, rfl, hp, hn⟩ := hlines l ml
          obtain ⟨b, hb⟩ := fun_line_total ops dops fops dm hnone n ((.cons e.1 e.2, .atom "true") :: S) pos negs hp hn
          refine ⟨b, fun m hm => ?_⟩
          obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          have h := hb m' hm'
          dsimp only at h ⊢
          rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-0-/1».pure]
          simpa [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-0-/2»] using h)
      refine ⟨lb, fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      have h := hlb m' hm'
      dsimp only at h ⊢
      simp only [Term.list] at dnf
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
      simp [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2», Elixir.Module.Types.Descr.«empty_bdd_seen_key/2»,
        Erlang.erlang.«is_map_key/2», fresh, Term.false, Erlang.maps.«put/3»,
        Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf, h])
  refine ⟨b, fun m hm => ?_⟩
  have h := hb m hm
  dsimp only at h ⊢
  unfold Elixir.Module.Types.Descr.«fun_empty?/2»
  simpa [Erlang.maps.«to_list/1»] using h

/-- Maps whose keys are among the six field names have at most six entries. -/
theorem entries_le_six {X : List (Term × Term)}
    (keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
      q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map") : (mapEntries X).length ≤ 6 := by
  have nd : ((mapEntries X).map Prod.fst).Nodup :=
    List.pairwise_map.mpr ((mapEntries_distinct X).imp fun h e => h (by rw [e]; exact compareExact_self _))
  have sub : (mapEntries X).map Prod.fst ⊆
      [.atom "bitmap", .atom "atom", .atom "fun", .atom "list", .atom "tuple", .atom "map"] := by
    intro q mq
    obtain ⟨e, me, rfl⟩ := List.mem_map.mp mq
    rcases keys e.1 (by rw [mapLookup_of_mem_mapEntries me]; rfl) with h | h | h | h | h | h <;> simp [h]
  simpa using nd.length_le_of_subset sub

theorem next_cons (k v rest : Term) :
    Erlang.maps.«next/1» (.cons (.tuple #[k, v]) rest) = .ok (.tuple #[k, v, rest]) := by
  simp [Erlang.maps.«next/1»]

/-- Checking that each field of the left type is covered gives the same Boolean at every call depth from `K`. -/
theorem iterator_sub_uni (K : Nat) (B : List (Term × Term)) :
    ∀ es : List (Term × Term),
      (∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∃ r, (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«bare_difference/3» (D m) e.1 e.2 y = .ok r) ∧
        (kept (e.1, r) = Bool.true →
          BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) e.1 r (.map [])))) →
      (∀ e ∈ es, mapLookup B e.1 = Option.none →
        BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) e.1 e.2 (.map []))) →
      BoolAt K (fun m => do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» (D m) it (.map B) (.map [])) := by
  intro es
  induction es with
  | nil =>
    intro _ _
    exact ⟨Bool.true, fun m _ => by
      dsimp only
      simp [Term.list, Erlang.maps.«next/1»]
      unfold Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3»
      rfl⟩
  | cons e rest ih =>
    intro both alone
    obtain ⟨bt, ht⟩ := ih (fun e' m => both e' (List.mem_cons_of_mem _ m)) (fun e' m => alone e' (List.mem_cons_of_mem _ m))
    obtain ⟨b₁, h₁⟩ : ∃ b₁ : Bool, ∀ m, K ≤ m → (do
        let it ← Erlang.maps.«next/1» (Term.list ((e :: rest).map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» (D m) it (.map B) (.map [])) =
          Lynx.Except.andAlso (.ok (boolAtom b₁)) (do
            let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
            Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» (D m) it (.map B) (.map [])) true := by
      cases hb : mapLookup B e.1 with
      | none =>
        obtain ⟨b₁, h₁⟩ := alone e List.mem_cons_self hb
        refine ⟨b₁, fun m hm => ?_⟩
        have e₁ := h₁ m hm
        dsimp only at e₁
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, hb, e₁]
      | some y =>
        obtain ⟨r, rr, kk⟩ := both e List.mem_cons_self y hb
        by_cases k : kept (e.1, r) = Bool.true
        · obtain ⟨eb, heb⟩ := kk k
          have ⟨z, b0⟩ : compareExact (fuel r (.integer 0)) r (.integer 0) ≠ .eq ∧ compareExact (fuel r (.atom "bdd_bot")) r (.atom "bdd_bot") ≠ .eq := by
            simpa [kept] using k
          refine ⟨eb, fun m hm => ?_⟩
          have e₁ := heb m hm
          dsimp only at e₁
          simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
          rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
          simp [getMapKeys_single, hb, rr m hm, z, b0, e₁, Lynx.Except.orElse]
        · refine ⟨Bool.true, fun m hm => ?_⟩
          simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
          rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
          rcases dropped (by simpa using k) with h | h <;> rw [h] at rr <;>
            simp [getMapKeys_single, hb, rr m hm, Lynx.Except.orElse]
    refine ⟨b₁ && bt, fun m hm => ?_⟩
    have e₂ := ht m hm
    dsimp only at e₂ ⊢
    rw [h₁ m hm, e₂, andAlso_bool]

/-- Static types decide subtyping, when each field of the left type does, at every call depth from `K`. -/
theorem subtype_maps (K : Nat) (A B : List (Term × Term)) (sA : mapLookup A (.atom "dynamic") = Option.none)
    (sB : mapLookup B (.atom "dynamic") = Option.none)
    (both : ∀ e ∈ mapEntries A, ∀ y, mapLookup B e.1 = some y → ∃ r, (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«bare_difference/3» (D m) e.1 e.2 y = .ok r) ∧
        (kept (e.1, r) = Bool.true →
          BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) e.1 r (.map []))))
    (alone : ∀ e ∈ mapEntries A, mapLookup B e.1 = Option.none →
        BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) e.1 e.2 (.map []))) :
    BoolAt K (fun m => Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B)) := by
  obtain ⟨b, hb⟩ := iterator_sub_uni K B (mapEntries A) both alone
  by_cases same : compareExact (fuel (.map B) (.map A)) (.map B) (.map A) = .eq
  · refine ⟨Bool.true, fun m _ => ?_⟩
    dsimp only
    unfold Elixir.Module.Types.Descr.«subtype?/2»
    simp [unfold_map, Erlang.erlang.«is_map_key/2», sA, sB, any_key, Lynx.Except.andAlso,
      Erlang.erlang.«/=/2»]
    unfold Elixir.Module.Types.Descr.«subtype_static?/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨b, fun m hm => ?_⟩
    have walk := hb m hm
    dsimp only at walk ⊢
    unfold Elixir.Module.Types.Descr.«subtype?/2»
    simp [unfold_map, Erlang.erlang.«is_map_key/2», sA, sB, any_key, Lynx.Except.andAlso,
      Erlang.erlang.«/=/2»]
    unfold Elixir.Module.Types.Descr.«subtype_static?/2»
    simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, sA, Erlang.maps.«iterator/1»]
    exact walk

/-- Looking for a non-empty common field gives the same Boolean at every call depth from `K` plus
the number of fields walked. -/
theorem iterator_disj_uni (K : Nat) (B : List (Term × Term)) :
    ∀ es : List (Term × Term),
      (∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∃ r, (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«bare_intersection/3» (D m) e.1 e.2 y = .ok r) ∧
        (kept (e.1, r) = Bool.true →
          BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) e.1 r (.map [])))) →
      BoolAt (K + es.length) (fun m => do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2» (D m) it (.map B)) := by
  intro es
  induction es with
  | nil =>
    intro _
    exact ⟨Bool.false, fun m _ => by
      dsimp only
      simp [Term.list, Erlang.maps.«next/1»]
      unfold Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2»
      rfl⟩
  | cons e rest ih =>
    intro both
    obtain ⟨bt, ht⟩ := ih (fun e' m => both e' (List.mem_cons_of_mem _ m))
    have cont : ∀ m x, K + rest.length + 1 ≤ m → (D m).pure (.function "Elixir.Module.Types.Descr"
        "-iterator_non_disjoint_intersection?/2-fun-0-" 1
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B]) #[x] = .ok (boolAtom bt) := by
      intro m x hm
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      have h := ht m' hm'
      dsimp only at h
      rw [Erlang.program.«Elixir.Module.Types.Descr:-iterator_non_disjoint_intersection?/2-fun-0-/1».pure]
      simpa [Elixir.Module.Types.Descr.«-iterator_non_disjoint_intersection?/2-fun-0-/3»] using h
    cases hb : mapLookup B e.1 with
    | none =>
      refine ⟨bt, fun m hm => ?_⟩
      dsimp only
      simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
      rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2».eq_def]
      simp [getMapKeys_single, hb, cont m _ (by simp at hm; omega)]
    | some y =>
      obtain ⟨r, rr, kk⟩ := both e List.mem_cons_self y hb
      by_cases k : kept (e.1, r) = Bool.true
      · obtain ⟨eb, heb⟩ := kk k
        have ⟨z, b0⟩ : compareExact (fuel r (.integer 0)) r (.integer 0) ≠ .eq ∧ compareExact (fuel r (.atom "bdd_bot")) r (.atom "bdd_bot") ≠ .eq := by
          simpa [kept] using k
        refine ⟨!eb || bt, fun m hm => ?_⟩
        have h := heb m (by simp at hm; omega)
        dsimp only at h ⊢
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2».eq_def]
        cases eb <;> simp [getMapKeys_single, hb, rr m (by simp at hm; omega), z, b0, h,
          Elixir.Module.Types.Descr.«empty_key?/2», Erlang.erlang.«=:=/2»,
          cont m _ (by simp at hm; omega)]
      · refine ⟨bt, fun m hm => ?_⟩
        dsimp only
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2».eq_def]
        rcases dropped (by simpa using k) with h | h <;> rw [h] at rr <;>
          simp [getMapKeys_single, hb, rr m (by simp at hm; omega),
            Erlang.erlang.«=:=/2», cont m _ (by simp at hm; omega)]

theorem subtype_term_l {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    (d : Dispatcher) (b : Term) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") b = Elixir.Module.Types.Descr.«subtype?/2» d (.map T) b := by
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [term]

theorem subtype_term_r {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«subtype?/2» d a (.atom "term") = Elixir.Module.Types.Descr.«subtype?/2» d a (.map T) := by
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [term]

/-- Static types decide subtyping when their fields subtract and decide emptiness. -/
theorem sub_fields (K : Nat) (F : String → Term → Prop) (A B : List (Term × Term))
    (sA : mapLookup A (.atom "dynamic") = Option.none) (sB : mapLookup B (.atom "dynamic") = Option.none)
    (kA : ∀ q, (mapLookup A q).isSome → ∃ name, q = .atom name)
    (fA : ∀ name w, mapLookup A (.atom name) = some w → F name w)
    (fB : ∀ name w, mapLookup B (.atom name) = some w → F name w)
    (diff : ∀ name x y, F name x → F name y → ∃ r, (∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → F name r))
    (empty : ∀ name x, F name x →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map []))) :
    BoolAt K (fun m => Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B)) := by
  refine subtype_maps K A B sA sB (fun e me y hy => ?_) (fun e me _ => ?_)
  · have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, key⟩ := kA e.1 (by rw [hx]; rfl)
    rw [key] at hx hy ⊢
    obtain ⟨r, rr, kr⟩ := diff name e.2 y (fA _ _ hx) (fB _ _ hy)
    exact ⟨r, rr, fun k => empty name r (kr k)⟩
  · have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, key⟩ := kA e.1 (by rw [hx]; rfl)
    rw [key] at hx ⊢
    exact empty name e.2 (fA _ _ hx)

/-- Static types decide disjointness when their fields intersect and decide emptiness, at every call depth
from `K + 6`, as each field walked costs a call. -/
theorem disj_fields (K : Nat) (F : String → Term → Prop) (A B : List (Term × Term))
    (sA : mapLookup A (.atom "dynamic") = Option.none) (sB : mapLookup B (.atom "dynamic") = Option.none)
    (kA : ∀ q, (mapLookup A q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
      q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map")
    (kB : ∀ q, (mapLookup B q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
      q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map")
    (fA : ∀ name w, mapLookup A (.atom name) = some w → F name w)
    (fB : ∀ name w, mapLookup B (.atom name) = some w → F name w)
    (inter : ∀ name x y, F name x → F name y → ∃ r, (∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → F name r))
    (empty : ∀ name x, F name x →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map []))) :
    BoolAt (K + 6) (fun m => Elixir.Module.Types.Descr.«disjoint?/2» (D m) (.map A) (.map B)) := by
  have name_of : ∀ (X : List (Term × Term)) q, (mapLookup X q).isSome →
      (q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨ q = .atom "list" ∨ q = .atom "tuple" ∨
        q = .atom "map") → ∃ name, q = .atom name := by
    intro X q _ h
    rcases h with h | h | h | h | h | h <;> exact ⟨_, h⟩
  have walk := fun (X Y : List (Term × Term)) (kX : ∀ q, (mapLookup X q).isSome → ∃ name, q = .atom name)
      (fX : ∀ name w, mapLookup X (.atom name) = some w → F name w)
      (fY : ∀ name w, mapLookup Y (.atom name) = some w → F name w) =>
    iterator_disj_uni K Y (mapEntries X) (fun e me y hy => by
      have hx := mapLookup_of_mem_mapEntries me
      obtain ⟨name, key⟩ := kX e.1 (by rw [hx]; rfl)
      rw [key] at hx hy ⊢
      obtain ⟨r, rr, kr⟩ := inter name e.2 y (fX _ _ hx) (fY _ _ hy)
      exact ⟨r, rr, fun k => empty name r (kr k)⟩)
  obtain ⟨ba, ha⟩ := walk A B (fun q h => name_of A q h (kA q h)) fA fB
  obtain ⟨bb, hb⟩ := walk B A (fun q h => name_of B q h (kB q h)) fB fA
  have lA := entries_le_six kA
  have lB := entries_le_six kB
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  refine ⟨if sa > sb then !bb else !ba, fun m hm => ?_⟩
  have e₁ := ha m (by omega)
  have e₂ := hb m (by omega)
  dsimp only at e₁ e₂ ⊢
  unfold Elixir.Module.Types.Descr.«disjoint?/2»
  simp [getMapKeys_single, sA, sB]
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2»
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1», e₂]
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1», e₁]

/-- The fields of a union of static types, with common fields combined by `g`. -/
def unionList (g : Term → Term → Term → Term) (L R : List (Term × Term)) : List (Term × Term) :=
  match L, R with
  | [], _ => R
  | _ :: _, [] => L
  | _ :: _, _ :: _ => mergeList g L R

theorem union_explicit (K : Nat) (L R : List (Term × Term)) (sL : mapLookup L (.atom "dynamic") = Option.none)
    (sR : mapLookup R (.atom "dynamic") = Option.none) (g : Term → Term → Term → Term)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y = .ok (g q x y)) :
    ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map L) (.map R) = .ok (.map (unionList g L R)) := by
  intro m hm
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  simp [getMapKeys_single, Erlang.erlang.«==/2», sL, sR]
  cases L with
  | nil => simp [unionList]
  | cons l ls =>
    cases R with
    | nil => simp [unionList]
    | cons r rs =>
      simp only [unionList]
      unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
      have run := merge_with_eq (D (n + 1)) "Elixir.Module.Types.Descr" "bare_union" #[] (l :: ls) (r :: rs) g (by
        intro e me x hx
        have hy := mapLookup_of_mem_mapEntries me
        rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure]
        exact calls e.1 x e.2 hx hy n hn)
      simpa using run

/-- Unions of static types whose common fields unite the same way at every call depth. -/
theorem union_uniform (K : Nat) (L R : List (Term × Term)) (sL : mapLookup L (.atom "dynamic") = Option.none)
    (sR : mapLookup R (.atom "dynamic") = Option.none) (keysR : ∀ q, (mapLookup R q).isSome → ∃ name, q = .atom name)
    (g : Term → Term → Term → Term)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y = .ok (g q x y)) :
    ∃ U, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map L) (.map R) = .ok (.map U)) ∧
      ∀ q, (mapLookup R q = Option.none → mapLookup U q = mapLookup L q) ∧
        (∀ y, mapLookup R q = some y → mapLookup L q = Option.none → mapLookup U q = some y) ∧
        (∀ x y, mapLookup L q = some x → mapLookup R q = some y → mapLookup U q = some (g q x y)) := by
  obtain ⟨U, run, look⟩ := union_any K L R sL sR keysR (fun q x y hx hy => ⟨_, calls q x y hx hy K (Nat.le_refl _)⟩)
  have same := (union_explicit K L R sL sR g calls (K + 1) (Nat.le_refl _)).symm.trans run
  simp only [Except.ok.injEq, Term.map.injEq] at same
  refine ⟨U, fun m hm => by rw [union_explicit K L R sL sR g calls m hm, same], fun q =>
    ⟨(look q).1, (look q).2.1, fun x y hx hy => (look q).2.2 x y _ hx hy (calls q x y hx hy K (Nat.le_refl _))⟩⟩

theorem union3_basic (name : String) (h : name = "bitmap" ∨ name = "atom") (d d' : Dispatcher) (x y : Term) :
    Elixir.Module.Types.Descr.«bare_union/3» d (.atom name) x y =
      Elixir.Module.Types.Descr.«bare_union/3» d' (.atom name) x y := by
  rcases h with rfl | rfl <;> simp [Elixir.Module.Types.Descr.«bare_union/3»]

theorem fun_top_union (n : Nat) :
    Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom "fun") (.tuple #[.atom "negation", .map []])
      (.tuple #[.atom "negation", .map []]) = .ok (.tuple #[.atom "negation", .map []]) := by
  have irun := intersect_with_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-fun_repr_intersection/2-fun-0-" #[]
    [] [] (fun _ _ _ => .nil) (by intro e me; simp at me)
  have frun := filter_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-symmetrical_intersection/3-fun-0-" #[]
    (interList (fun _ _ _ => .nil) [] []) kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  have r0 : ([] : List (Option (Term × Term))).reduceOption = [] := rfl
  simp only [interList, filterList, mapEntries_nil, List.map_nil, r0] at irun frun
  simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
    Elixir.Module.Types.Descr.«fun_repr_intersection/2»]
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [irun, frun]

/-- Basic fields unite into basic fields. -/
theorem fieldok_union (name : String) {x y : Term} (hx : FieldOk name x) (hy : FieldOk name y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y = .ok r) ∧ FieldOk name r := by
  rcases hx with ⟨rfl, bx⟩ | ⟨rfl, ax⟩ | ⟨nb, na, tx⟩
  · rcases hy with ⟨-, by'⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · obtain ⟨w, run, fw, -⟩ := bit_union (D 1) bx by'
      exact ⟨w, fun n => by rw [union3_basic _ (Or.inl rfl) _ (D 1), run], Or.inl ⟨rfl, fw⟩⟩
    · simp at e
    · exact absurd rfl e
  · rcases hy with ⟨e, -⟩ | ⟨-, ay⟩ | ⟨-, e, -⟩
    · simp at e
    · obtain ⟨w, run, fw, -⟩ := atom_union_spec (D 1) ax ay
      exact ⟨w, fun n => by rw [union3_basic _ (Or.inr rfl) _ (D 1), run], Or.inr (Or.inl ⟨rfl, fw⟩)⟩
    · exact absurd rfl e
  · rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, ty⟩
    · exact absurd e nb
    · exact absurd e na
    rw [tx] at ty
    cases ty
    refine ⟨x, fun n => ?_, Or.inr (Or.inr ⟨nb, na, tx⟩)⟩
    by_cases f : name = "fun"
    · subst f; simp [topValue] at tx; subst tx; exact fun_top_union n
    by_cases l : name = "list"
    · subst l; simp [topValue] at tx; subst tx
      simp [Elixir.Module.Types.Descr.«bare_union/3»]; unfold Elixir.Module.Types.Descr.«list_union/2»; rfl
    by_cases t : name = "tuple"
    · subst t; simp [topValue] at tx; subst tx
      simp [Elixir.Module.Types.Descr.«bare_union/3»]; unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl
    by_cases m : name = "map"
    · subst m; simp [topValue] at tx; subst tx
      simp [Elixir.Module.Types.Descr.«bare_union/3»]; unfold Elixir.Module.Types.Descr.«map_union/2»; rfl
    · simp [topValue] at tx

/-- Basic fields are not empty. -/
theorem fieldok_empty (d : Dispatcher) (name : String) {x : Term} (hx : FieldOk name x) :
    Elixir.Module.Types.Descr.«empty_key?/3» d (.atom name) x (.map []) = .ok (.atom "false") := by
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨nb, na, tx⟩
  · rfl
  · rfl
  · by_cases f : name = "fun"
    · subst f; simp [topValue] at tx; subst tx
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using fun_top_nonempty d (.map [])
    by_cases l : name = "list"
    · subst l; simp [topValue] at tx; subst tx
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using list_top_nonempty d (.map [])
    by_cases t : name = "tuple"
    · subst t; simp [topValue] at tx; subst tx
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using tuple_top_nonempty d seenOk_nil
    by_cases m : name = "map"
    · subst m; simp [topValue] at tx; subst tx
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using map_top_nonempty d seenOk_nil
    · simp [topValue] at tx

/-! Nested element types: types of basic bitmap and atom fields, whose function, list, tuple, and map
types hold types of a smaller nesting. -/

def NField (E : Term → Prop) (name : String) (w : Term) : Prop :=
  (name ≠ "tuple" ∧ name ≠ "map" ∧ name ≠ "list" ∧ name ≠ "fun" ∧ FieldOk name w) ∨ (name = "fun" ∧ FField E w) ∨
    (name = "tuple" ∧ OField (TupleOk E) w) ∨ (name = "map" ∧ OField (MapOk E) w) ∨ (name = "list" ∧ Bdd (LLit E) w)

structure NestFields (E : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
    q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
  fields : ∀ name w, mapLookup X (.atom name) = some w → NField E name w

def NestC (E : Term → Prop) (t : Term) : Prop := t = .atom "term" ∨ ∃ X, t = .map X ∧ NestFields E X

theorem NestFields.static {X : List (Term × Term)} (n : NestFields E X) :
    mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w => rcases n.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e

theorem NestFields.atomKey {X : List (Term × Term)} (n : NestFields E X) {q w : Term} (h : mapLookup X q = some w) :
    ∃ name, q = .atom name := by
  rcases n.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem Basic.nest (hterm : E (.atom "term")) {M : List (Term × Term)} (basic : Basic M) : NestFields E M := by
  refine ⟨basic.keys, fun name w h => ?_⟩
  have f := basic.field h
  by_cases t : name = "tuple"
  · subst t
    rcases f with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · simp at e
    · simp at e
    · simp [topValue] at tv; subst tv; exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩))
  by_cases m : name = "map"
  · subst m
    rcases f with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · simp at e
    · simp at e
    · simp [topValue] at tv; subst tv; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, rfl⟩⟩)))
  by_cases l : name = "list"
  · subst l
    rcases f with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · simp at e
    · simp at e
    · simp [topValue] at tv; subst tv
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Bdd.leaf_iff.mpr ⟨46675407, _, _, rfl, hterm, hterm⟩⟩)))
  by_cases fn : name = "fun"
  · subst fn
    rcases f with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · simp at e
    · simp at e
    · simp [topValue] at tv; subst tv
      exact Or.inr (Or.inl ⟨rfl, Bool.false, [], rfl, fun q v h => by simp [mapLookup] at h⟩)
  exact Or.inl ⟨t, m, l, fn, f⟩

theorem tuple_inter_closure {x y : Term} (fx : OField (TupleOk E) x) (fy : OField (TupleOk E) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (TupleOk E) w) := by
  obtain ⟨w, run, k, -⟩ := open_inter_spec tupleOk_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
    tuple_inter_shape.2.2 (.atom "tuple") fx fy
  exact ⟨w, run, fun kw => (k kw).1⟩

theorem map_inter_closure {x y : Term} (fx : OField (MapOk E) x) (fy : OField (MapOk E) y) :
    ∃ w, Elixir.Module.Types.Descr.«map_intersection/2» x y = .ok w ∧
      (kept (.atom "map", w) = Bool.true → OField (MapOk E) w) := by
  obtain ⟨w, run, k, -⟩ := open_inter_spec mapOk_not _ map_inter_shape.1 map_inter_shape.2.1
    map_inter_shape.2.2 (.atom "map") fx fy
  exact ⟨w, run, fun kw => (k kw).1⟩

theorem leaf_new_term : ∃ h : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.atom "term"]) =
      .ok (.tuple #[.integer h, .atom "open", Term.list [.atom "term"]]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
  refine ⟨(1 <<< 27) + hash, ?_⟩
  simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2»,
    Erlang.erlang.«is_list/1», Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
  rfl

theorem tuple_diff_closure (hterm : E (.atom "term")) {x y : Term} (fx : OField (TupleOk E) x)
    (fy : OField (TupleOk E) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (TupleOk E) w) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl,
      fun k => by simp [kept] at k⟩
  have ny := not_top_of_ok wy tupleOk_not
  by_cases special : ∃ k, y = .tuple #[k, .atom "closed", .nil]
  · obtain ⟨k, rfl⟩ := special
    rcases fx with ⟨kt, rfl⟩ | wx
    · obtain ⟨h, run⟩ := leaf_new_term
      refine ⟨_, by simp [Elixir.Module.Types.Descr.«tuple_difference/2», Erlang.erlang.«==/2», run], fun _ =>
        Or.inr (Bdd.leaf_iff.mpr ⟨⟨h, "open", [.atom "term"], rfl, Or.inl rfl, fun e me => by
          rw [List.mem_singleton.mp me]; exact hterm⟩, fun ⟨_, e⟩ => by simp [Term.list] at e⟩)⟩
    · by_cases openLeaf : ∃ kx e, x = .tuple #[kx, .atom "open", e]
      · obtain ⟨kx, e, rfl⟩ := openLeaf
        have ne : e ≠ .nil := fun h => not_top_of_ok wx tupleOk_not _ (by rw [h])
        refine ⟨_, ?_, fun _ => Or.inr wx⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        cases e <;> simp_all [Erlang.erlang.«==/2»]
      · obtain ⟨w, run, keep, -⟩ := diff_ok wx wy
        exact ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx tupleOk_not) ny (fun ⟨h, _⟩ => openLeaf h), run],
          fun _ => Or.inr (keep _ wx wy)⟩
  · rcases fx with ⟨kt, rfl⟩ | wx
    · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [diff_leaf_top]
      · refine ⟨_, ?_, fun _ => Or.inl ⟨kt, rfl⟩⟩
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [diff_leaf_bot]
      · obtain ⟨w, run, keep, -⟩ := neg_ok wy
        refine ⟨w, ?_, fun _ => Or.inr (keep _ wy)⟩
        rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
      · obtain ⟨w, run, keep, -⟩ := neg_ok wy
        refine ⟨w, ?_, fun _ => Or.inr (keep _ wy)⟩
        rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
    · obtain ⟨w, run, keep, -⟩ := diff_ok wx wy
      exact ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx tupleOk_not) ny (fun ⟨_, h⟩ => special h), run],
        fun _ => Or.inr (keep _ wx wy)⟩

theorem map_diff_closure {x y : Term} (fx : OField (MapOk E) x) (fy : OField (MapOk E) y) :
    ∃ w, Elixir.Module.Types.Descr.«map_difference/2» x y = .ok w ∧
      (kept (.atom "map", w) = Bool.true → OField (MapOk E) w) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl,
      fun k => by simp [kept] at k⟩
  have ny := not_top_of_ok wy mapOk_not
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_top]
    · refine ⟨_, ?_, fun _ => Or.inl ⟨kt, rfl⟩⟩
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_bot]
    · obtain ⟨w, run, keep, -⟩ := neg_ok wy
      exact ⟨w, by rw [map_difference_neg ny _ rfl, run], fun _ => Or.inr (keep _ wy)⟩
    · obtain ⟨w, run, keep, -⟩ := neg_ok wy
      exact ⟨w, by rw [map_difference_neg ny _ rfl, run], fun _ => Or.inr (keep _ wy)⟩
  · obtain ⟨w, run, keep, -⟩ := diff_ok wx wy
    exact ⟨w, by rw [map_difference_bdd (not_top_of_ok wx mapOk_not) ny, run], fun _ => Or.inr (keep _ wx wy)⟩

theorem list_inter_closure {x y : Term} (wx : Bdd (LLit E) x) (wy : Bdd (LLit E) y) :
    ∃ w, Elixir.Module.Types.Descr.«list_intersection/2» x y = .ok w ∧ Bdd (LLit E) w := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    exact ⟨y, by unfold Elixir.Module.Types.Descr.«list_intersection/2»; rfl, wy⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    refine ⟨x, ?_, wx⟩
    unfold Elixir.Module.Types.Descr.«list_intersection/2»
    split
    · exact absurd ⟨_, rfl⟩ tx
    · rfl
    · exfalso; simp_all
  obtain ⟨w, run, keep, -⟩ := inter_ok wx wy
  refine ⟨w, ?_, keep _ wx wy⟩
  unfold Elixir.Module.Types.Descr.«list_intersection/2»
  split
  · exact absurd ⟨_, rfl⟩ tx
  · exact absurd ⟨_, rfl⟩ ty
  · exact run

theorem list_diff_closure {x y : Term} (wx : Bdd (LLit E) x) (wy : Bdd (LLit E) y) :
    ∃ w, Elixir.Module.Types.Descr.«list_difference/2» x y = .ok w ∧ Bdd (LLit E) w := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
    · obtain ⟨k', rfl⟩ := ty
      exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«list_difference/2»; rfl, Bdd.bot⟩
    obtain ⟨w, run, keep, -⟩ := neg_ok wy
    refine ⟨w, ?_, keep _ wy⟩
    unfold Elixir.Module.Types.Descr.«list_difference/2»
    split
    · exact absurd ⟨_, rfl⟩ ty
    · exact run
    · exfalso; simp_all
  obtain ⟨w, run, keep, -⟩ := diff_ok wx wy
  refine ⟨w, ?_, keep _ wx wy⟩
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact absurd ⟨_, rfl⟩ tx
  · exact absurd ⟨_, rfl⟩ tx
  · exact run

theorem map_size_ne {M : List (Term × Term)} (hM : M ≠ []) :
    ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
  cases M with
  | nil => exact absurd rfl hM
  | cons e rest => exact size_cons e rest

/-- Function results whose unions have no arities become `0`. -/
theorem fun_result {pos : Bool} {M : List (Term × Term)} (bM : AllBddP (FunArity E) M)
    (e : Nat → Except Exception Term)
    (h₁ : pos = Bool.false → ∀ n, e n = .ok (.tuple #[.atom "negation", .map M]))
    (h₂ : pos = Bool.true → M = [] → ∀ n, e n = .ok (.integer 0))
    (h₃ : pos = Bool.true → M ≠ [] → ∀ n, e n = .ok (.tuple #[.atom "union", .map M])) :
    ∃ r, (∀ n, e n = .ok r) ∧ (kept (.atom "fun", r) = Bool.true → FField E r) := by
  cases pos
  · exact ⟨_, h₁ rfl, fun _ => ⟨Bool.false, M, rfl, bM⟩⟩
  · by_cases hM : M = []
    · exact ⟨_, h₂ rfl hM, fun k => by simp [kept] at k⟩
    · exact ⟨_, h₃ rfl hM, fun _ => ⟨Bool.true, M, rfl, bM⟩⟩

theorem ffield_inter {x y : Term} (fx : FField E x) (fy : FField E y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") x y = .ok r) ∧
      (kept (.atom "fun", r) = Bool.true → FField E r) := by
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, -⟩ := repr_union_uniform b₁ b₂
    refine fun_result (pos := Bool.false) bM _ (fun _ n => ?_) (fun h => by cases h) (fun h => by cases h)
    simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
      Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, bM, run, -⟩ := repr_diff_uniform b₂ b₁
    refine fun_result (pos := Bool.true) bM _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, -⟩ := repr_diff_uniform b₁ b₂
    refine fun_result (pos := Bool.true) bM _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, -⟩ := repr_inter_uniform b₁ b₂
    refine fun_result (pos := Bool.true) bM _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

theorem ffield_diff {x y : Term} (fx : FField E x) (fy : FField E y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun") x y = .ok r) ∧
      (kept (.atom "fun", r) = Bool.true → FField E r) := by
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, -⟩ := repr_diff_uniform b₂ b₁
    refine fun_result (pos := Bool.true) bM _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, -⟩ := repr_union_uniform b₁ b₂
    refine fun_result (pos := Bool.false) bM _ (fun _ n => ?_) (fun h => by cases h) (fun h => by cases h)
    simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
      Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, bM, run, -⟩ := repr_inter_uniform b₁ b₂
    refine fun_result (pos := Bool.true) bM _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, -⟩ := repr_diff_uniform b₁ b₂
    refine fun_result (pos := Bool.true) bM _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

theorem ffield_union {x y : Term} (fx : FField E x) (fy : FField E y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom "fun") x y = .ok r) ∧ FField E r := by
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, -⟩ := repr_inter_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      Bool.false, M, rfl, bM⟩
  · obtain ⟨M, bM, run, -⟩ := repr_diff_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      Bool.false, M, rfl, bM⟩
  · obtain ⟨M, bM, run, -⟩ := repr_diff_uniform b₂ b₁
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      Bool.false, M, rfl, bM⟩
  · obtain ⟨M, bM, run, -⟩ := repr_union_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      Bool.true, M, rfl, bM⟩

theorem nfield_inter {name : String} {x y : Term} (hx : NField E name x) (hy : NField E name y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → NField E name r) := by
  rcases hx with ⟨nt, nm, nl, nf, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩
  · rcases hy with ⟨-, -, -, -, fy⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨r, run, ok, -⟩ := inter_key name x y fx fy
      exact ⟨r, fun _ => run _, fun k => Or.inl ⟨nt, nm, nl, nf, ok k⟩⟩
    · exact absurd rfl nf
    · exact absurd rfl nt
    · exact absurd rfl nm
    · exact absurd rfl nl
  · rcases hy with ⟨-, -, -, n, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · obtain ⟨r, run, k⟩ := ffield_inter fx fy
      exact ⟨r, run, fun kw => Or.inr (Or.inl ⟨rfl, k kw⟩)⟩
    all_goals simp at e
  · rcases hy with ⟨n, -, -, -, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · simp at e
    · obtain ⟨w, run, k⟩ := tuple_inter_closure fx fy
      exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run],
        fun kw => Or.inr (Or.inr (Or.inl ⟨rfl, k kw⟩))⟩
    all_goals simp at e
  · rcases hy with ⟨-, n, -, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · simp at e
    · simp at e
    · obtain ⟨w, run, k⟩ := map_inter_closure fx fy
      exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run],
        fun kw => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k kw⟩)))⟩
    · simp at e
  · rcases hy with ⟨-, -, n, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩
    · exact absurd rfl n
    all_goals try simp at e
    obtain ⟨w, run, k⟩ := list_inter_closure fx fy
    exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run],
      fun _ => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k⟩)))⟩

theorem nfield_diff (hterm : E (.atom "term")) {name : String} {x y : Term} (hx : NField E name x)
    (hy : NField E name y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → NField E name r) := by
  rcases hx with ⟨nt, nm, nl, nf, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩
  · rcases hy with ⟨-, -, -, -, fy⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨r, run, ok, -⟩ := diff_key name x y fx fy
      exact ⟨r, fun _ => run _, fun k => Or.inl ⟨nt, nm, nl, nf, ok k⟩⟩
    · exact absurd rfl nf
    · exact absurd rfl nt
    · exact absurd rfl nm
    · exact absurd rfl nl
  · rcases hy with ⟨-, -, -, n, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · obtain ⟨r, run, k⟩ := ffield_diff fx fy
      exact ⟨r, run, fun kw => Or.inr (Or.inl ⟨rfl, k kw⟩)⟩
    all_goals simp at e
  · rcases hy with ⟨n, -, -, -, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · simp at e
    · obtain ⟨w, run, k⟩ := tuple_diff_closure hterm fx fy
      exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run],
        fun kw => Or.inr (Or.inr (Or.inl ⟨rfl, k kw⟩))⟩
    all_goals simp at e
  · rcases hy with ⟨-, n, -, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · simp at e
    · simp at e
    · obtain ⟨w, run, k⟩ := map_diff_closure fx fy
      exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run],
        fun kw => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k kw⟩)))⟩
    · simp at e
  · rcases hy with ⟨-, -, n, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩
    · exact absurd rfl n
    all_goals try simp at e
    obtain ⟨w, run, k⟩ := list_diff_closure fx fy
    exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run],
      fun _ => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k⟩)))⟩

theorem nest_inter (A B : List (Term × Term)) (nA : NestFields E A) (nB : NestFields E B) :
    ∃ C, (∀ m, 1 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map A) (.map B) =
      .ok (.map C)) ∧ NestFields E C ∧ ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (D 1) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have ik := fun name x y (hx : mapLookup A (.atom name) = some x) (hy : mapLookup B (.atom name) = some y) =>
    nfield_inter (nA.fields name x hx) (nB.fields name y hy)
  have gval : ∀ name x y r, (∀ n, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom name) x y =
      .ok r) → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h 0]
  obtain ⟨I, C, run, lookI, lookC⟩ := inter_uniform 1 A B nA.static nB.static g (by
    intro q x y hx hy m hm
    obtain ⟨name, key⟩ := nA.atomKey hx
    subst key
    obtain ⟨r, run, -⟩ := ik name x y hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run, gval _ _ _ _ run])
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup A (.atom name), mapLookup B (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    intro name
    rw [lookC, find_atom, lookI, find_atom]
    cases mapLookup A (.atom name) <;> cases hR : mapLookup B (.atom name) <;> simp [hR]
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have hI := find_isSome I q hit
      rw [lookI] at hI
      split at hI
      · rename_i e' hit'
        exact find_isSome A q hit'
      · simp at hI
    · simp at some
  refine ⟨C, run, ⟨fun q h => nA.keys q (keys q h), fun name w h => ?_⟩, keys⟩
  rw [look] at h
  cases hx : mapLookup A (.atom name) <;> cases hy : mapLookup B (.atom name) <;> rw [hx, hy] at h <;>
    try simp at h
  rename_i x y
  obtain ⟨r, run, ok⟩ := ik name x y hx hy
  simp only [gval _ _ _ _ run] at h
  obtain ⟨k, rfl⟩ := h
  exact ok k

theorem nest_diff_fold (hterm : E (.atom "term")) (left : Term) (A B : List (Term × Term)) (nA : NestFields E A)
    (nB : NestFields E B)
    (hleft : left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧
      Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) :
    ∃ C, (∀ m, 3 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) left (.map B) = .ok (.map C)) ∧
      NestFields E C ∧ ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
  by_cases emptyB : B = []
  · subst emptyB
    rcases hleft with rfl | ⟨-, ne, -⟩
    rotate_left
    · exact absurd rfl ne
    refine ⟨A, fun m _ => ?_, nA, fun q h => h⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2»]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (D 1) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have gval : ∀ name x y r, (∀ n, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom name) x y =
      .ok r) → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h 0]
  have fold := fun depth => difference_fold (depth + 1) (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries B) A (mapEntries_distinct B) (by
      intro e member v₁ found
      have hy := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := nA.atomKey found
      rw [key] at found hy ⊢
      obtain ⟨r, run, -⟩ := nfield_diff hterm (nA.fields name v₁ found) (nB.fields name e.2 hy)
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, run, gval _ _ _ _ run])
  obtain ⟨C, -, lookC, eqC⟩ := fold 0
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup B (.atom name) with
      | some y => (mapLookup A (.atom name)).bind fun x =>
          if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | none => mapLookup A (.atom name) := by
    intro name
    rw [lookC, find_atom]
    cases mapLookup B (.atom name) <;> rfl
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have same : compareExact (fuel q e.1) q e.1 = .eq := by simpa using List.find?_some hit
      rw [mapLookup_congr same]
      cases h : mapLookup A e.1 <;> simp_all
    · exact some
  refine ⟨C, fun m hm => ?_, ⟨fun q h => nA.keys q (keys q h), fun name w h => ?_⟩, keys⟩
  · obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 1 + 2 := ⟨m - 3, by omega⟩
    obtain ⟨C', fold', -, eq'⟩ := fold depth
    rw [eqC, ← eq']
    rcases hleft with rfl | ⟨rfl, -, term⟩
    · unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2», unfold_map, static_map nA.static, static_map nB.static, emptyB]
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3»]
      simpa using fold'
    · unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2», unfold_map, static_map nB.static, emptyB]
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3», term]
      simpa using fold'
  · rw [look] at h
    cases hy : mapLookup B (.atom name) with
    | none => rw [hy] at h; exact nA.fields name w h
    | some y =>
      rw [hy] at h
      cases hx : mapLookup A (.atom name) with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        obtain ⟨r, run, ok⟩ := nfield_diff hterm (nA.fields name x hx) (nB.fields name y hy)
        simp only [gval _ _ _ _ run, Option.bind_some] at h
        split at h
        · rename_i k; cases h; exact ok k
        · cases h

/-- The emptiness of nested types does not depend on the call depth. -/
theorem nest_empty (ops : ElemOk E K) (dops : ElemDiff E K) (_hnone : E (.map [])) (tail : TailOk E)
    {M : List (Term × Term)}
    (nM : NestFields E M) (S : List (Term × Term))
    (funB : ∃ fb, ∀ w, mapLookup M (.atom "fun") = some w → ∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«fun_empty?/2» (D m) w (.map S) = .ok (boolAtom fb)) :
    ∃ b, ∀ m, K + 2 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map M) (.map S) = .ok (boolAtom b) := by
  by_cases nonempty : M = []
  · subst nonempty
    exact ⟨Bool.true, fun m _ => by simpa [boolAtom] using empty_none_seen (D m) (.map S)⟩
  have static : mapLookup M (.atom "dynamic") = Option.none := nM.static
  have listB : ∃ lb, ∀ w, mapLookup M (.atom "list") = some w → ∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«list_empty?/2» (D m) w (.map S) = .ok (boolAtom lb) := by
    cases h : mapLookup M (.atom "list") with
    | none => exact ⟨Bool.false, fun w hw => by cases hw⟩
    | some w =>
      rcases nM.fields _ w h with ⟨-, -, e, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, f⟩
      · exact absurd rfl e
      · simp at e
      · simp at e
      · simp at e
      · obtain ⟨lb, hlb⟩ := list_total ops dops tail S f
        exact ⟨lb, fun w' hw' m hm => by cases hw'; exact hlb m hm⟩
  have tupleB : ∃ tb, ∀ w, mapLookup M (.atom "tuple") = some w → ∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) w (.map S) = .ok (boolAtom tb) := by
    cases h : mapLookup M (.atom "tuple") with
    | none => exact ⟨Bool.false, fun w hw => by cases hw⟩
    | some w =>
      rcases nM.fields _ w h with ⟨e, -, -, -, -⟩ | ⟨e, -⟩ | ⟨-, f⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · exact absurd rfl e
      · simp at e
      · obtain ⟨tb, htb⟩ := tuple_total ops dops S f
        exact ⟨tb, fun w' hw' m hm => by cases hw'; exact htb m (by omega)⟩
      · simp at e
      · simp at e
  have mapB : ∃ mb, ∀ w, mapLookup M (.atom "map") = some w → ∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«map_empty?/2» (D m) w (.map S) = .ok (boolAtom mb) := by
    cases h : mapLookup M (.atom "map") with
    | none => exact ⟨Bool.false, fun w hw => by cases hw⟩
    | some w =>
      rcases nM.fields _ w h with ⟨-, e, -, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, f⟩ | ⟨e, -⟩
      · exact absurd rfl e
      · simp at e
      · simp at e
      · obtain ⟨mb, hmb⟩ := map_total ops dops S f
        exact ⟨mb, fun w' hw' m hm => by cases hw'; exact hmb m hm⟩
      · simp at e
  obtain ⟨tb, ht⟩ := tupleB
  obtain ⟨mb, hm⟩ := mapB
  obtain ⟨lb, hl⟩ := listB
  obtain ⟨fb, hf⟩ := funB
  refine ⟨!(mapLookup M (.atom "atom")).isSome && !(mapLookup M (.atom "bitmap")).isSome &&
    (!(mapLookup M (.atom "tuple")).isSome || tb) && (!(mapLookup M (.atom "map")).isSome || mb) &&
    (!(mapLookup M (.atom "list")).isSome || lb) && (!(mapLookup M (.atom "fun")).isSome || fb), fun m hmk => ?_⟩
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  cases ha : mapLookup M (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso, boolAtom]
  | none =>
  cases hb : mapLookup M (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  | none =>
  have tB := fun w h => ht w h m (by omega)
  have mB := fun w h => hm w h m hmk
  have lB := fun w h => hl w h m (by omega)
  have fB := fun w h => hf w h m hmk
  clear ht hm hl hf
  have ab : ∀ x y : Bool,
      Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (boolAtom y)) Bool.true = .ok (boolAtom (x && y)) := by
    intro x y; cases x <;> cases y <;> rfl
  have abT : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "true")) Bool.true = .ok (boolAtom x) := by
    intro x; cases x <;> rfl
  have abF : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "false")) Bool.true = .ok (.atom "false") := by
    intro x; cases x <;> rfl
  have bt : boolAtom Bool.true = .atom "true" := rfl
  have bf : boolAtom Bool.false = .atom "false" := rfl
  cases htu : mapLookup M (.atom "tuple") <;> cases hma : mapLookup M (.atom "map") <;>
    cases hli : mapLookup M (.atom "list") <;> cases hfu : mapLookup M (.atom "fun") <;>
    simp [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», ab, abT, bt, ha, hb, htu, hma, hli,
      hfu, tB, mB, lB, fB]

theorem list_union_closure {x y : Term} (wx : Bdd (LLit E) x) (wy : Bdd (LLit E) y) :
    ∃ w, Elixir.Module.Types.Descr.«list_union/2» x y = .ok w ∧ Bdd (LLit E) w := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    exact ⟨_, by unfold Elixir.Module.Types.Descr.«list_union/2»; rfl, wx⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    refine ⟨_, ?_, wy⟩
    unfold Elixir.Module.Types.Descr.«list_union/2»
    split
    · exact absurd ⟨_, rfl⟩ tx
    · rename_i _ heq; rw [← heq]; rfl
    · exfalso; simp_all
  obtain ⟨w, run, keep, -⟩ := union_ok wx wy
  refine ⟨w, ?_, keep _ wx wy⟩
  unfold Elixir.Module.Types.Descr.«list_union/2»
  split
  · exact absurd ⟨_, rfl⟩ tx
  · exact absurd ⟨_, rfl⟩ ty
  · exact run

theorem nfield_union {name : String} {x y : Term} (hx : NField E name x)
    (hy : NField E name y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y = .ok r) ∧ NField E name r := by
  rcases hx with ⟨nt, nm, nl, nf, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩
  · rcases hy with ⟨-, -, -, -, fy⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨r, run, ok⟩ := fieldok_union name fx fy
      exact ⟨r, run, Or.inl ⟨nt, nm, nl, nf, ok⟩⟩
    · exact absurd rfl nf
    · exact absurd rfl nt
    · exact absurd rfl nm
    · exact absurd rfl nl
  · rcases hy with ⟨-, -, -, n, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · obtain ⟨r, run, k⟩ := ffield_union fx fy
      exact ⟨r, run, Or.inr (Or.inl ⟨rfl, k⟩)⟩
    all_goals simp at e
  · rcases hy with ⟨n, -, -, -, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · simp at e
    · obtain ⟨w, run, fw, -⟩ := open_union_spec tupleOk_not _ tuple_union_shape.1 tuple_union_shape.2.1
        tuple_union_shape.2.2 fx fy
      exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))⟩
    all_goals simp at e
  · rcases hy with ⟨-, n, -, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩ | ⟨e, -⟩
    · exact absurd rfl n
    · simp at e
    · simp at e
    · obtain ⟨w, run, fw, -⟩ := open_union_spec mapOk_not _ map_union_shape.1 map_union_shape.2.1
        map_union_shape.2.2 fx fy
      exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run],
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))⟩
    · simp at e
  · rcases hy with ⟨-, -, n, -, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fy⟩
    · exact absurd rfl n
    all_goals try simp at e
    obtain ⟨w, run, k⟩ := list_union_closure fx fy
    exact ⟨w, fun _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k⟩)))⟩

/-- Fields of nested types decide their emptiness at every call depth from `K + 5`. -/
theorem nfield_empty (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (dm : DomOk Dm E K)
    (hnone : E (.map [])) (tail : TailOk E) {name : String} {x : Term} (hx : NField E name x)
    (S : List (Term × Term)) :
    BoolAt (K + 5) (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S)) := by
  rcases hx with ⟨nt, nm, nl, nf, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩ | ⟨rfl, fx⟩
  · rcases fx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨nb, na, tx⟩
    · exact ⟨Bool.false, fun m _ => rfl⟩
    · exact ⟨Bool.false, fun m _ => rfl⟩
    · simp [topValue] at tx
  · obtain ⟨b, hb⟩ := fun_total ops dops fops dm hnone fx S
    exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty_key?/3»; exact hb m hm⟩
  · obtain ⟨b, hb⟩ := tuple_total ops dops S fx
    exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty_key?/3»; exact hb m (by omega)⟩
  · obtain ⟨b, hb⟩ := map_total ops dops S fx
    exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty_key?/3»; exact hb m (by omega)⟩
  · obtain ⟨b, hb⟩ := list_total ops dops tail S fx
    exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty_key?/3»; exact hb m (by omega)⟩

/-- Unions of nested types are nested types, whose fields are fields of either type. -/
theorem nest_union (A B : List (Term × Term)) (nA : NestFields E A)
    (nB : NestFields E B) :
    ∃ U, (∀ m, 1 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B) = .ok (.map U)) ∧
      NestFields E U ∧ ∀ q, (mapLookup U q).isSome → (mapLookup A q).isSome ∨ (mapLookup B q).isSome := by
  let g : Term → Term → Term → Term := fun q x y =>
    match Elixir.Module.Types.Descr.«bare_union/3» (D 1) q x y with | .ok w => w | .error _ => .nil
  have gval : ∀ name x y r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y =
      .ok r) → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h 0]
  have calls : ∀ q x y, mapLookup A q = some x → mapLookup B q = some y → ∀ m, 1 ≤ m →
      Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y = .ok (g q x y) := by
    intro q x y hx hy m hm
    obtain ⟨name, rfl⟩ := nA.atomKey hx
    obtain ⟨r, run, -⟩ := nfield_union (nA.fields name x hx) (nB.fields name y hy)
    obtain ⟨n, rfl, -⟩ := succ_of_le hm
    rw [run, gval _ _ _ _ run]
  obtain ⟨U, run, look⟩ := union_uniform 1 A B nA.static nB.static (fun q h => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h; exact nB.atomKey hw) g calls
  have keys : ∀ q, (mapLookup U q).isSome → (mapLookup A q).isSome ∨ (mapLookup B q).isSome := by
    intro q h
    cases hb : mapLookup B q with
    | none => rw [(look q).1 hb] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  refine ⟨U, run, ⟨fun q h => ?_, fun name w h => ?_⟩, keys⟩
  · rcases keys q h with h | h
    · exact nA.keys q h
    · exact nB.keys q h
  · cases hb : mapLookup B (.atom name) with
    | none => rw [(look _).1 hb] at h; exact nA.fields name w h
    | some y =>
      cases ha : mapLookup A (.atom name) with
      | none => rw [(look _).2.1 y hb ha] at h; rw [← Option.some.inj h]; exact nB.fields name y hb
      | some x =>
        rw [(look _).2.2 x y ha hb] at h
        rw [← Option.some.inj h]
        obtain ⟨r, run, ok⟩ := nfield_union (nA.fields name x ha) (nB.fields name y hb)
        rw [gval _ _ _ _ run]
        exact ok

/-- Domains of nested function types: maps of tuples of element types. -/
def TupC (E : Term → Prop) (t : Term) : Prop :=
  ∃ X, t = .map X ∧ NestFields E X ∧ ∀ q, (mapLookup X q).isSome → q = .atom "tuple"

theorem domOk (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (hnone : E (.map []))
    (tail : TailOk E) : DomOk (TupC E) E (K + 3) := by
  have hterm := ops.term
  refine ⟨fun l hl => ?_, ⟨[], rfl, ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩,
    fun q h => by simp [mapLookup] at h⟩, fun ⟨X, e, _⟩ => ⟨X, e⟩, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_,
    fun {a b} ha hb => ?_, fun {a} ha S => ?_⟩
  · obtain ⟨k, run⟩ := args_domain l fun e me => fops.static (hl e me)
    have look : ∀ q, mapLookup [(Term.atom "tuple", Term.tuple #[.integer k, .atom "closed", Term.list l])] q =
        if compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq then some (.tuple #[.integer k, .atom "closed", Term.list l])
        else Option.none := by
      intro q; by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq <;> simp [mapLookup, e]
    refine ⟨_, ⟨_, rfl, ⟨fun q h => ?_, fun name w h => ?_⟩, fun q h => ?_⟩, run⟩
    · rw [look] at h; split at h
      · rename_i e; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((compareExact_eq_atom _ _).mp e)))))
      · simp at h
    · rw [look] at h; split at h
      · rename_i e
        simp only [atom_compareExact_eq, Term.atom.injEq] at e
        subst e
        simp at h; subst h
        exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Bdd.leaf_iff.mpr
          ⟨⟨k, "closed", l, rfl, Or.inr rfl, hl⟩, fun ⟨_, e⟩ => by simp at e⟩)⟩))
      · simp at h
    · rw [look] at h; split at h
      · rename_i e; exact (compareExact_eq_atom _ _).mp e
      · simp at h
  · obtain ⟨A, rfl, nA, tA⟩ := ha
    obtain ⟨B, rfl, nB, tB⟩ := hb
    obtain ⟨U, run, nU, keys⟩ := nest_union A B nA nB
    exact ⟨_, ⟨U, rfl, nU, fun q h => (keys q h).elim (tA q) (tB q)⟩, fun m hm => run m (by omega)⟩
  · obtain ⟨A, rfl, nA, tA⟩ := ha
    obtain ⟨B, rfl, nB, -⟩ := hb
    obtain ⟨C, run, nC, keys⟩ := nest_inter A B nA nB
    exact ⟨_, ⟨C, rfl, nC, fun q h => tA q (keys q h)⟩, fun m hm => run m (by omega)⟩
  · obtain ⟨A, rfl, nA, tA⟩ := ha
    obtain ⟨B, rfl, nB, -⟩ := hb
    obtain ⟨C, run, nC, keys⟩ := nest_diff_fold hterm (.map A) A B nA nB (Or.inl rfl)
    exact ⟨_, ⟨C, rfl, nC, fun q h => tA q (keys q h)⟩, fun m hm => run m (by omega)⟩
  · obtain ⟨A, rfl, nA, tA⟩ := ha
    obtain ⟨b, hb⟩ := nest_empty ops dops hnone tail nA S ⟨Bool.false, fun w h => by
      have := tA _ (by rw [h]; rfl); simp at this⟩
    exact ⟨b, fun m hm => hb m (by omega)⟩

theorem nestOk (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (hnone : E (.map []))
    (tail : TailOk E) : ElemOk (NestC E) (K + 8) := by
  have dm := domOk ops dops fops hnone tail
  refine ⟨Or.inl rfl, fun {a b} ha hb => ?_, fun {a} ha S => ?_,
    Or.inr ⟨[], rfl, ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩⟩, by omega⟩
  · rcases ha with rfl | ⟨A, rfl, nA⟩
    · exact ⟨b, hb, fun _ _ => by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl⟩
    rcases hb with rfl | ⟨B, rfl, nB⟩
    · exact ⟨_, Or.inr ⟨A, rfl, nA⟩, fun m _ => inter_term_right _ _⟩
    obtain ⟨C, run, nC, -⟩ := nest_inter A B nA nB
    exact ⟨_, Or.inr ⟨C, rfl, nC⟩, fun m hm => run m (by omega)⟩
  · rcases ha with rfl | ⟨M, rfl, nM⟩
    · exact ⟨Bool.false, fun m _ => by rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl⟩
    · have funB : ∃ fb, ∀ w, mapLookup M (.atom "fun") = some w → ∀ m, K + 6 + 2 ≤ m →
          Elixir.Module.Types.Descr.«fun_empty?/2» (D m) w (.map S) = .ok (boolAtom fb) := by
        cases h : mapLookup M (.atom "fun") with
        | none => exact ⟨Bool.false, fun w hw => by cases hw⟩
        | some w =>
          rcases nM.fields _ w h with ⟨-, -, -, n, -⟩ | ⟨-, f⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
          · exact absurd rfl n
          · obtain ⟨fb, hfb⟩ := fun_total (ops.mono (Nat.le_add_right K 3)) (dops.mono (Nat.le_add_right K 3))
              ⟨fops.static, fun ha hb => let ⟨c, hc, run⟩ := fops.union ha hb; ⟨c, hc, fun m hm => run m (by omega)⟩,
                fun ha hb => (fops.sub ha hb).mono (by omega), fun ha hb => (fops.disj ha hb).mono (by omega)⟩
              dm hnone f S
            exact ⟨fb, fun w' hw' m hm => by cases hw'; exact hfb m (by omega)⟩
          all_goals simp at e
      exact nest_empty (ops.mono (Nat.le_add_right K 6)) (dops.mono (Nat.le_add_right K 6)) hnone tail nM S funB

theorem nestDiff (hterm : E (.atom "term")) (K : Nat) : ElemDiff (NestC E) (K + 3) := by
  refine ⟨fun {a b} ha hb => ?_⟩
  rcases hb with rfl | ⟨B, rfl, nB⟩
  · exact ⟨_, Or.inr ⟨[], rfl, ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩⟩,
      fun m _ => diff_term_right _ _⟩
  by_cases empty : B = []
  · subst empty
    refine ⟨a, ha, fun m _ => ?_⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
  rcases ha with rfl | ⟨A, rfl, nA⟩
  · obtain ⟨T, term, -⟩ := unfolded_term_fields
    obtain ⟨C, run, nC, -⟩ := nest_diff_fold hterm (.atom "term") T B (Basic.nest hterm (term_basic term).1) nB
      (Or.inr ⟨rfl, empty, term⟩)
    exact ⟨_, Or.inr ⟨C, rfl, nC⟩, fun m hm => run m (by omega)⟩
  · obtain ⟨C, run, nC, -⟩ := nest_diff_fold hterm (.map A) A B nA nB (Or.inl rfl)
    exact ⟨_, Or.inr ⟨C, rfl, nC⟩, fun m hm => run m (by omega)⟩

theorem nest_none : NestC E (.map []) :=
  Or.inr ⟨[], rfl, ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩⟩

/-- `list_tail_unfold/1` of the top type: the top type without lists. -/
def tailTerm : List (Term × Term) :=
  [(.atom "bitmap", .integer 255), (.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil]),
    (.atom "fun", .tuple #[.atom "negation", .map []]),
    (.atom "map", .tuple #[.integer 61102469, .atom "open", .nil]),
    (.atom "atom", .tuple #[.atom "negation", .map []])]

theorem tailTerm_basic : Basic tailTerm := by
  refine basic_of (fun q h => ?_) fun name w h => ?_
  · obtain ⟨e, me, qe⟩ := (mapLookup_isSome _ _).mp h
    simp only [tailTerm, List.mem_cons, List.mem_nil_iff, or_false] at me
    rcases me with rfl | rfl | rfl | rfl | rfl <;> rw [(compareExact_eq_atom _ _).mp qe] <;> simp
  · have look : ∀ n, mapLookup tailTerm (.atom n) =
        if n = "bitmap" then some (.integer 255) else if n = "tuple" then
          some (.tuple #[.integer 61102469, .atom "open", .nil]) else if n = "fun" then
          some (.tuple #[.atom "negation", .map []]) else if n = "map" then
          some (.tuple #[.integer 61102469, .atom "open", .nil]) else if n = "atom" then
          some (.tuple #[.atom "negation", .map []]) else none := by
      intro n
      simp only [tailTerm, mapLookup, List.find?]
      by_cases b : n = "bitmap" <;> by_cases t : n = "tuple" <;> by_cases f : n = "fun" <;>
        by_cases m : n = "map" <;> by_cases a : n = "atom" <;> simp_all
    rw [look] at h
    split at h
    · rename_i e; subst e; cases h; exact Or.inl ⟨rfl, 255, rfl, by decide, by decide⟩
    split at h
    · rename_i e; subst e; cases h; exact Or.inr (Or.inr ⟨by decide, by decide, rfl⟩)
    split at h
    · rename_i e; subst e; cases h; exact Or.inr (Or.inr ⟨by decide, by decide, rfl⟩)
    split at h
    · rename_i e; subst e; cases h; exact Or.inr (Or.inr ⟨by decide, by decide, rfl⟩)
    split at h
    · rename_i e; subst e; cases h
      exact Or.inr (Or.inl ⟨rfl, ⟨Bool.false, [], rfl, by simp [Erlang.sets.elements?]⟩,
        atom_nonempty Bool.false [] (by simp)⟩)
    · cases h

def noList (M : List (Term × Term)) : List (Term × Term) :=
  M.filter fun e => compareExact (fuel (.atom "list") e.1) (.atom "list") e.1 != .eq

theorem tail_map (d : Dispatcher) (M : List (Term × Term)) :
    Elixir.Module.Types.Descr.«list_tail_unfold/1» d (.map M) = .ok (.map (noList M)) := by
  unfold Elixir.Module.Types.Descr.«list_tail_unfold/1»
  simp [Erlang.maps.«remove/2», noList]

theorem noList_lookup (M : List (Term × Term)) (q : Term) (h : (mapLookup (noList M) q).isSome) :
    mapLookup (noList M) q = mapLookup M q := by
  simp only [noList, mapLookup_filter] at h ⊢
  split at h
  · simp at h
  · rename_i n; simp [n]

theorem Basic.noList {M : List (Term × Term)} (basic : Basic M) : Basic (noList M) := by
  refine basic_of (fun q h => basic.keys q (by rw [← noList_lookup M q h]; exact h)) fun name w h => ?_
  have := noList_lookup M (.atom name) (by rw [h]; rfl)
  rw [this] at h
  exact basic.field h

theorem NestFields.noList {M : List (Term × Term)} (n : NestFields E M) : NestFields E (noList M) := by
  refine ⟨fun q h => n.keys q (by rw [← noList_lookup M q h]; exact h), fun name w h => ?_⟩
  have := noList_lookup M (.atom name) (by rw [h]; rfl)
  rw [this] at h
  exact n.fields name w h

/-- Types with the fields of `tailTerm`, in any order, are basic. -/
theorem basic_of_lookup {T : List (Term × Term)} (h : ∀ q, mapLookup T q = mapLookup tailTerm q) : Basic T := by
  have b := tailTerm_basic
  refine ⟨fun q hq => b.keys q (by rw [← h]; exact hq), fun w hw => b.bitmap w (by rw [← h]; exact hw),
    fun w hw => ?_, fun name w nb na hw => b.top name w nb na (by rw [← h]; exact hw)⟩
  obtain ⟨af, q, hq⟩ := b.atom w (by rw [← h]; exact hw)
  exact ⟨af, q, by simpa [amem, h] using hq⟩

theorem lookup_tail_perm {T : List (Term × Term)}
    (h : ∀ name, mapLookup T (.atom name) = mapLookup tailTerm (.atom name))
    (keys : ∀ q, (mapLookup T q).isSome → ∃ name : String, q = .atom name) :
    ∀ q, mapLookup T q = mapLookup tailTerm q := by
  intro q
  by_cases a : ∃ name : String, q = .atom name
  · obtain ⟨name, rfl⟩ := a; exact h name
  · have n₁ : mapLookup T q = Option.none := by
      cases e : mapLookup T q with
      | none => rfl
      | some _ => exact absurd (keys q (by simp [e])) a
    have n₂ : mapLookup tailTerm q = Option.none := by
      cases e : mapLookup tailTerm q with
      | none => rfl
      | some w => exact absurd (tailTerm_basic.atomKey e) a
    rw [n₁, n₂]

/-- The top type without lists, whatever order its fields come in. -/
theorem tail_term : ∃ T, (∀ d, Elixir.Module.Types.Descr.«list_tail_unfold/1» d (.atom "term") = .ok (.map T)) ∧
    Basic T := by
  refine ⟨_, fun d => by unfold Elixir.Module.Types.Descr.«list_tail_unfold/1»; rfl, ?_⟩
  refine basic_of_lookup (lookup_tail_perm (fun name => ?_) fun q h => ?_)
  · simp only [mapLookup, List.find?, tailTerm, compareExact_eq_atom, Term.atom.injEq]
    all_goals by_cases b : name = "bitmap" <;> by_cases t : name = "tuple" <;> by_cases f : name = "fun" <;>
      by_cases m : name = "map" <;> by_cases a : name = "atom" <;> simp_all
  · by_cases a : ∃ name : String, q = .atom name
    · exact a
    · have na : ∀ k : String, ¬q = .atom k := fun k e => a ⟨k, e⟩
      simp [mapLookup, List.find?, compareExact_eq_atom, na] at h

theorem tail_lelem : TailOk LElem := by
  intro e he
  rcases he with rfl | ⟨M, rfl, bM⟩
  · obtain ⟨T, run, bT⟩ := tail_term
    exact ⟨.map T, fun m _ => run (D m), Or.inr ⟨T, rfl, bT⟩⟩
  · exact ⟨_, fun m _ => tail_map (D m) M, Or.inr ⟨_, rfl, bM.noList⟩⟩

theorem tail_nest (hterm : E (.atom "term")) : TailOk (NestC E) := by
  intro e he
  rcases he with rfl | ⟨M, rfl, nM⟩
  · obtain ⟨T, run, bT⟩ := tail_term
    exact ⟨.map T, fun m _ => run (D m), Or.inr ⟨T, rfl, Basic.nest hterm bT⟩⟩
  · exact ⟨_, fun m _ => tail_map (D m) M, Or.inr ⟨_, rfl, nM.noList⟩⟩

theorem ElemFun.mono {E : Term → Prop} {K K' : Nat} (fops : ElemFun E K) (le : K ≤ K') : ElemFun E K' :=
  ⟨fops.static, fun ha hb => let ⟨c, hc, run⟩ := fops.union ha hb; ⟨c, hc, fun m hm => run m (by omega)⟩,
    fun ha hb => (fops.sub ha hb).mono le, fun ha hb => (fops.disj ha hb).mono le⟩

theorem union_term_l (d : Dispatcher) (b : Term) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.atom "term") b = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»; rfl

theorem union_term_r (d : Dispatcher) (A : List (Term × Term)) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map A) (.atom "term") = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»; rfl

theorem disjoint_term_l (d : Dispatcher) (b : Term) :
    Elixir.Module.Types.Descr.«disjoint?/2» d (.atom "term") b = Elixir.Module.Types.Descr.«empty?/1» d b := by
  unfold Elixir.Module.Types.Descr.«disjoint?/2»; rfl

theorem disjoint_term_r (d : Dispatcher) (A : List (Term × Term)) :
    Elixir.Module.Types.Descr.«disjoint?/2» d (.map A) (.atom "term") =
      Elixir.Module.Types.Descr.«empty?/1» d (.map A) := by
  unfold Elixir.Module.Types.Descr.«disjoint?/2»; rfl

/-- Classes of the top type and static maps decide subtyping and disjointness from their fields. -/
theorem class_sub_disj (C : Term → Prop) (F : String → Term → Prop) (P : List (Term × Term) → Prop) (K : Nat)
    (hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ A, a = .map A ∧ P A)
    (top : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧ P T)
    (static : ∀ {A}, P A → mapLookup A (.atom "dynamic") = Option.none)
    (keys : ∀ {A}, P A → ∀ q, (mapLookup A q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
      q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map")
    (fields : ∀ {A}, P A → ∀ name w, mapLookup A (.atom name) = some w → F name w)
    (diff : ∀ name x y, F name x → F name y → ∃ r, (∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → F name r))
    (inter : ∀ name x y, F name x → F name y → ∃ r, (∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → F name r))
    (empty : ∀ name x, F name x →
      BoolAt K (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map [])))
    (emptyC : ∀ {a}, C a → BoolAt K (fun m => Elixir.Module.Types.Descr.«empty?/1» (D m) a)) :
    (∀ {a b}, C a → C b → BoolAt K (fun m => Elixir.Module.Types.Descr.«subtype?/2» (D m) a b)) ∧
      (∀ {a b}, C a → C b → BoolAt (K + 6) (fun m => Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b)) := by
  obtain ⟨T, term, pT⟩ := top
  have kA : ∀ {A}, P A → ∀ q, (mapLookup A q).isSome → ∃ name, q = .atom name := fun pA q h => by
    rcases keys pA q h with e | e | e | e | e | e <;> exact ⟨_, e⟩
  have toMap : ∀ {a}, C a → ∃ A, P A ∧ ∀ d b,
      Elixir.Module.Types.Descr.«subtype?/2» d a b = Elixir.Module.Types.Descr.«subtype?/2» d (.map A) b := by
    intro a ha
    rcases hC ha with rfl | ⟨A, rfl, pA⟩
    · exact ⟨T, pT, fun d b => subtype_term_l term d b⟩
    · exact ⟨A, pA, fun _ _ => rfl⟩
  have toMapR : ∀ {b}, C b → ∃ B, P B ∧ ∀ d A,
      Elixir.Module.Types.Descr.«subtype?/2» d (.map A) b = Elixir.Module.Types.Descr.«subtype?/2» d (.map A) (.map B) := by
    intro b hb
    rcases hC hb with rfl | ⟨B, rfl, pB⟩
    · exact ⟨T, pT, fun d A => subtype_term_r term d (.map A)⟩
    · exact ⟨B, pB, fun _ _ => rfl⟩
  refine ⟨fun {a b} ha hb => ?_, fun {a b} ha hb => ?_⟩
  · obtain ⟨A, pA, ea⟩ := toMap ha
    obtain ⟨B, pB, eb⟩ := toMapR hb
    obtain ⟨r, hr⟩ := sub_fields K F A B (static pA) (static pB) (kA pA) (fields pA) (fields pB) diff empty
    exact ⟨r, fun m hm => by dsimp only; rw [ea, eb]; exact hr m hm⟩
  · rcases hC ha with rfl | ⟨A, rfl, pA⟩
    · obtain ⟨r, hr⟩ := emptyC hb
      exact ⟨r, fun m hm => by dsimp only; rw [disjoint_term_l]; exact hr m (by omega)⟩
    rcases hC hb with rfl | ⟨B, rfl, pB⟩
    · obtain ⟨r, hr⟩ := emptyC ha
      exact ⟨r, fun m hm => by dsimp only; rw [disjoint_term_r]; exact hr m (by omega)⟩
    exact disj_fields K F A B (static pA) (static pB) (keys pA) (keys pB) (fields pA) (fields pB) inter empty

theorem nestFun (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (hnone : E (.map []))
    (tail : TailOk E) : ElemFun (NestC E) (K + 14) := by
  have hterm := ops.term
  have dm := domOk ops dops fops hnone tail
  have nops := nestOk ops dops fops hnone tail
  have empty : ∀ name x, NField E name x →
      BoolAt (K + 8) (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map [])) :=
    fun name x hx => nfield_empty (ops.mono (Nat.le_add_right K 3)) (dops.mono (Nat.le_add_right K 3))
      (fops.mono (Nat.le_add_right K 3)) dm hnone tail hx []
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  obtain ⟨sub, disj⟩ := class_sub_disj (NestC E) (NField E) (NestFields E) (K + 8)
    (fun ha => ha) ⟨T, term, Basic.nest hterm (term_basic term).1⟩ (fun pA => pA.static) (fun pA => pA.keys)
    (fun pA => pA.fields)
    (fun name x y hx hy => by
      obtain ⟨r, run, k⟩ := nfield_diff hterm hx hy
      exact ⟨r, fun m hm => by obtain ⟨n, rfl, -⟩ := succ_of_le (show 1 ≤ m by omega); exact run n, k⟩)
    (fun name x y hx hy => by
      obtain ⟨r, run, k⟩ := nfield_inter hx hy
      exact ⟨r, fun m hm => by obtain ⟨n, rfl, -⟩ := succ_of_le (show 1 ≤ m by omega); exact run n, k⟩)
    empty
    (fun {a} ha => by
      rcases ha with rfl | ⟨A, rfl, nA⟩
      · exact ⟨Bool.false, fun m _ => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; rfl⟩
      · obtain ⟨b, hb⟩ := nops.empty (Or.inr ⟨A, rfl, nA⟩) []
        exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; exact hb m hm⟩)
  refine ⟨fun {a} ha => ?_, fun {a b} ha hb => ?_, fun ha hb => (sub ha hb).mono (by omega), disj⟩
  · rcases ha with rfl | ⟨A, rfl, nA⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨A, rfl, nA.static⟩)
  · rcases ha with rfl | ⟨A, rfl, nA⟩
    · exact ⟨_, Or.inl rfl, fun m _ => union_term_l _ _⟩
    rcases hb with rfl | ⟨B, rfl, nB⟩
    · exact ⟨_, Or.inl rfl, fun m _ => union_term_r _ _⟩
    obtain ⟨U, run, nU, -⟩ := nest_union A B nA nB
    exact ⟨_, Or.inr ⟨U, rfl, nU⟩, fun m hm => run m (by omega)⟩

/-- Unions of basic types are basic types. -/
theorem basic_union (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B) :
    ∃ U, (∀ m, 1 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B) = .ok (.map U)) ∧
      Basic U := by
  let g : Term → Term → Term → Term := fun q x y =>
    match Elixir.Module.Types.Descr.«bare_union/3» (D 1) q x y with | .ok w => w | .error _ => .nil
  have gval : ∀ name x y r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y =
      .ok r) → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h 0]
  have atomKey : ∀ {X : List (Term × Term)}, Basic X → ∀ {q w : Term}, mapLookup X q = some w →
      ∃ name, q = .atom name := fun bX q w h => by
    rcases bX.keys q (by rw [h]; rfl) with e | e | e | e | e | e <;> exact ⟨_, e⟩
  have calls : ∀ q x y, mapLookup A q = some x → mapLookup B q = some y → ∀ m, 1 ≤ m →
      Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y = .ok (g q x y) := by
    intro q x y hx hy m hm
    obtain ⟨name, rfl⟩ := atomKey bA hx
    obtain ⟨r, run, -⟩ := fieldok_union name (bA.field hx) (bB.field hy)
    obtain ⟨n, rfl, -⟩ := succ_of_le hm
    rw [run, gval _ _ _ _ run]
  obtain ⟨U, run, look⟩ := union_uniform 1 A B bA.static bB.static (fun q h => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h; exact atomKey bB hw) g calls
  refine ⟨U, run, basic_of (fun q h => ?_) fun name w h => ?_⟩
  · cases hb : mapLookup B q with
    | none => rw [(look q).1 hb] at h; exact bA.keys q h
    | some y => exact bB.keys q (by simp [hb])
  · cases hb : mapLookup B (.atom name) with
    | none => rw [(look _).1 hb] at h; exact bA.field h
    | some y =>
      cases ha : mapLookup A (.atom name) with
      | none => rw [(look _).2.1 y hb ha] at h; rw [← Option.some.inj h]; exact bB.field hb
      | some x =>
        rw [(look _).2.2 x y ha hb] at h
        rw [← Option.some.inj h]
        obtain ⟨r, run, ok⟩ := fieldok_union name (bA.field ha) (bB.field hb)
        rw [gval _ _ _ _ run]
        exact ok

theorem lelemFun : ElemFun LElem 8 := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  obtain ⟨sub, disj⟩ := class_sub_disj LElem FieldOk Basic 2 (fun ha => ha) ⟨T, term, (term_basic term).1⟩
    (fun bA => bA.static) (fun bA => bA.keys) (fun bA _ _ h => bA.field h)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok, -⟩ := diff_key name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok, -⟩ := inter_key name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x hx => ⟨Bool.false, fun m _ => fieldok_empty (D m) name hx⟩)
    (fun {a} ha => by
      rcases ha with rfl | ⟨A, rfl, bA⟩
      · exact ⟨Bool.false, fun m _ => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; rfl⟩
      · obtain ⟨b, hb⟩ := lelemOk.empty (Or.inr ⟨A, rfl, bA⟩) []
        exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; exact hb m hm⟩)
  refine ⟨fun {a} ha => ?_, fun {a b} ha hb => ?_, fun ha hb => (sub ha hb).mono (by omega), disj⟩
  · rcases ha with rfl | ⟨A, rfl, bA⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨A, rfl, bA.static⟩)
  · rcases ha with rfl | ⟨A, rfl, bA⟩
    · exact ⟨_, Or.inl rfl, fun m _ => union_term_l _ _⟩
    rcases hb with rfl | ⟨B, rfl, bB⟩
    · exact ⟨_, Or.inl rfl, fun m _ => union_term_r _ _⟩
    obtain ⟨U, run, bU⟩ := basic_union A B bA bB
    exact ⟨_, Or.inr ⟨U, rfl, bU⟩, fun m hm => run m (by omega)⟩

end Elixir.STTDescrProofsTest
