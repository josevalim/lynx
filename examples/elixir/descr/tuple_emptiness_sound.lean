namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple emptiness is sound: a tuple of values in a line makes its emptiness check answer `false`. -/

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

theorem full_of_val (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S)
    {e : Term} (he : E e) {y : V} (hy : den e y) : Full E K S e := by
  obtain ⟨b, run⟩ := ops.empty he S
  refine ⟨he, fun m hm => ?_⟩
  cases b
  · simpa [boolAtom] using run m hm
  · exact absurd hy ((sem.empty he hS hm (run m hm)).mp rfl y)

theorem full_of_inT (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S)
    {c : Bool} : ∀ {l : List Term} {v : List V}, (∀ e ∈ l, E e) → InT den c l v → ∀ e ∈ l, Full E K S e
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => h.elim
  | x :: l, y :: v, hl, h => by
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact full_of_val ops sem hS (hl _ List.mem_cons_self) h.1
    · exact full_of_inT ops sem hS (fun e m => hl e (List.mem_cons_of_mem _ m)) h.2 e me

theorem inT_fill_closed : ∀ {l : List Term} {v : List V}, InT den Bool.false l v →
    (∀ y, den (Term.atom "term") y) → InT den Bool.true (l ++ List.replicate (v.length - l.length) (Term.atom "term")) v
  | [], [], _, _ => trivial
  | [], y :: v, _, t => by
    have := inT_fill_closed (l := []) (v := v) (InT.open_nil v) t
    simp only [List.nil_append, List.length_cons, List.length_nil, Nat.sub_zero] at this ⊢
    rw [List.replicate_succ]
    exact ⟨t y, this⟩
  | _ :: _, [], h, _ => h.elim
  | e :: l, y :: v, h, t => by
    have len : (y :: v).length - (e :: l).length = v.length - l.length := by simp
    rw [len, List.cons_append]
    exact ⟨h.1, inT_fill_closed h.2 t⟩

theorem inT_fill_open : ∀ {l : List Term} {v : List V} (j : Nat), InT den Bool.false l v → l.length + j ≤ v.length →
    (∀ y, den (Term.atom "term") y) → InT den Bool.false (l ++ List.replicate j (Term.atom "term")) v
  | [], v, j, _, le, t => by
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at le ⊢
    induction j generalizing v with
    | zero => exact InT.open_nil v
    | succ j ih =>
      cases v with
      | nil => simp at le
      | cons y v => exact ⟨t y, ih v (InT.open_nil v) (by simp at le; omega)⟩
  | _ :: _, [], _, h, _, _ => h.elim
  | e :: l, y :: v, j, h, le, t => ⟨h.1, inT_fill_open j h.2 (by simp at le ⊢; omega) t⟩

/-- `tuple_empty_sizes?/5` answers false when a closed line of a size it checks answers false. -/
theorem sizes_false (d : Dispatcher) (l : List Term) (m' : Nat) (rest S : Term)
    (lines : ∀ i, l.length ≤ i → i < m' → ∃ b : Bool, Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed")
      (Term.list (l ++ List.replicate (i - l.length) (Term.atom "term"))) rest S = .ok (boolAtom b))
    (j : Nat) (lj : l.length ≤ j) (jm : j < m')
    (hj : Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed")
      (Term.list (l ++ List.replicate (j - l.length) (Term.atom "term"))) rest S = .ok (Term.atom "false")) :
    ∀ i, l.length ≤ i → i ≤ j → Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer i) (.integer m')
      (Term.list l) rest S = .ok (.atom "false") := by
  intro i le ij
  induction h : j - i generalizing i with
  | zero =>
    have : i = j := by omega
    subst this
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have lt : (i : Int) < m' := by omega
    simp [lt, fill_list l i le, hj, Lynx.Except.andAlso]
  | succ k ih =>
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have lt : (i : Int) < m' := by omega
    have next := ih (i + 1) (by omega) (by omega) (by omega)
    simp only [Int.natCast_add, Int.natCast_one] at next
    obtain ⟨b, hb⟩ := lines i le (by omega)
    simp only [Lynx.Except.guard, Erlang.erlang.«</2»]
    simp [Int.compare_eq_lt, lt, fill_list l i le, hb, next]
    cases b <;> rfl

theorem empty_false_of_val (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S)
    {m : Nat} (hm : K ≤ m) {e : Term} (he : E e) {y : V} (hy : den e y) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) e (.map S) = .ok (.atom "false") :=
  (full_of_val ops sem hS he hy).2 m hm

/-- `tuple_elements_empty?/6` answers false when a tuple of the line, outside the remaining negations, escapes the
negated literal at one of the positions it checks. -/
theorem elements_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) (c : Bool) (negs : List Term)
    (line : ∀ l : List Term, (∀ e ∈ l, E e) → ∀ v, InT den c l v → (∀ N ∈ negs, ¬LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "false"))
    (lineBool : ∀ l : List Term, (∀ e ∈ l, Full E K S e) → ∃ b : Bool,
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (boolAtom b)) :
    ∀ (nrest acc rest : List Term), (∀ e ∈ nrest, E e) → (∀ e ∈ acc, E e) → (∀ e ∈ rest, E e) →
      (c = Bool.true → nrest.length ≤ rest.length) → ∀ (v₁ w : List V), InT den Bool.true acc.reverse v₁ →
      InT den c rest w → (∀ N ∈ negs, ¬LitSem den N (v₁ ++ w)) → ¬InT den Bool.false nrest w →
      nrest.length ≤ w.length →
      Elixir.Module.Types.Descr.«tuple_elements_empty?/6» (D m) (Term.list acc) (.atom (if c then "closed" else "open"))
        (Term.list rest) (Term.list nrest) (Term.list negs) (.map S) = .ok (.atom "false") := by
  intro nrest
  induction nrest with
  | nil => intro _ _ _ _ _ _ v₁ w _ _ _ nI _; exact absurd (InT.open_nil w) nI
  | cons nt nl ih =>
    intro acc rest hn hacc hrest hlen v₁ w h₁ hw hneg nI wlen
    have hnt := hn nt List.mem_cons_self
    have hnl : ∀ e ∈ nl, E e := fun e m => hn e (List.mem_cons_of_mem _ m)
    obtain ⟨y, w', rfl⟩ : ∃ y w', w = y :: w' := by
      cases w with
      | nil => simp at wlen
      | cons y w' => exact ⟨y, w', rfl⟩
    obtain ⟨ty, es, hshape, hty, hes, hy, hw'⟩ : ∃ ty es, ((rest = [] ∧ ty = .atom "term" ∧ es = []) ∨ rest = ty :: es) ∧
        E ty ∧ (∀ e ∈ es, E e) ∧ den ty y ∧ InT den c es w' := by
      cases rest with
      | nil =>
        have hc : c = Bool.false := by
          cases c
          · rfl
          · have := hlen rfl; simp at this
        subst hc
        exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, ops.term, by simp, sem.term y, InT.open_nil w'⟩
      | cons x xs =>
        exact ⟨x, xs, Or.inr rfl, hrest x List.mem_cons_self, fun e m => hrest e (List.mem_cons_of_mem _ m), hw.1, hw.2⟩
    have hlen' : c = Bool.true → nl.length ≤ es.length := fun hc => by
      have := hlen hc
      rcases hshape with ⟨rfl, -, rfl⟩ | rfl <;> simp at this ⊢ <;> omega
    have accFull : ∀ e ∈ acc.reverse, Full E K S e :=
      full_of_inT ops sem hS (fun e me => hacc e (List.mem_reverse.mp me)) h₁
    have esFull : ∀ e ∈ es, Full E K S e := full_of_inT ops sem hS hes hw'
    have lineAt : ∀ x, E x → den x y → ∀ N ∈ negs, ¬LitSem den N (v₁ ++ y :: w') →
        InT den c (acc.reverse ++ x :: es) (v₁ ++ y :: w') := by
      intro x hx hxy _ _ _
      exact (InT.append _).mpr ⟨v₁, y :: w', rfl, h₁, hxy, hw'⟩
    have elemsLine : ∀ x, E x → ∀ e ∈ acc.reverse ++ x :: es, E e := by
      intro x hx e me
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at me
      rcases me with me | rfl | me
      · exact hacc e me
      · exact hx
      · exact hes e me
    obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty hnt
    have step := elements_step (D m) acc (.atom (if c then "closed" else "open")) rest nt nl (Term.list negs) (.map S)
      ty es hshape meet (hmeet m hm)
    have dmeet := sem.inter hty hnt hm (hmeet m hm)
    obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty hnt
    have ddiff := sem.diff hty hnt hm (hdiff m hm)
    obtain ⟨bm, em⟩ := ops.empty lmeet S
    obtain ⟨bd, ed⟩ := ops.empty ldiff S
    by_cases inN : den nt y
    · -- the tuple escapes later
      have nI' : ¬InT den Bool.false nl w' := fun h => nI ⟨inN, h⟩
      have meetFalse := empty_false_of_val ops sem hS hm lmeet ((dmeet y).mpr ⟨hy, inN⟩)
      cases bd
      · have r := ih (meet :: acc) es hnl (fun e me => by
            rcases List.mem_cons.mp me with rfl | me
            · exact lmeet
            · exact hacc e me) hes hlen' (v₁ ++ [y]) w' (by
            simp only [List.reverse_cons]
            exact (InT.append _).mpr ⟨v₁, [y], rfl, h₁, (dmeet y).mpr ⟨hy, inN⟩, trivial⟩) hw'
          (by simpa using hneg) nI' (by simp at wlen; omega)
        obtain ⟨bl, hl⟩ := lineBool (acc.reverse ++ diff :: es) fun e me => by
          simp only [List.mem_append, List.mem_cons] at me
          rcases me with me | rfl | me
          · exact accFull e me
          · exact ⟨ldiff, fun m' h' => by simpa [boolAtom] using ed m' h'⟩
          · exact esFull e me
        rw [(step.2 _ meetFalse (hdiff m hm)).2 (by simpa [boolAtom] using ed m hm), hl, r]
        cases bl <;> rfl
      · rw [(step.2 _ meetFalse (hdiff m hm)).1 (by simpa [boolAtom] using ed m hm)]
        exact ih (ty :: acc) es hnl (fun e me => by
            rcases List.mem_cons.mp me with rfl | me
            · exact hty
            · exact hacc e me) hes hlen' (v₁ ++ [y]) w' (by
            simp only [List.reverse_cons]
            exact (InT.append _).mpr ⟨v₁, [y], rfl, h₁, hy, trivial⟩) hw'
          (by simpa using hneg) nI' (by simp at wlen; omega)
    · -- the tuple escapes here
      cases bm
      · have diffFalse := empty_false_of_val ops sem hS hm ldiff ((ddiff y).mpr ⟨hy, inN⟩)
        rw [(step.2 _ (by simpa [boolAtom] using em m hm) (hdiff m hm)).2 diffFalse]
        rw [line (acc.reverse ++ diff :: es) (elemsLine diff ldiff) (v₁ ++ y :: w')
          ((InT.append _).mpr ⟨v₁, y :: w', rfl, h₁, (ddiff y).mpr ⟨hy, inN⟩, hw'⟩) hneg]
        rfl
      · rw [step.1 (by simpa [boolAtom] using em m hm)]
        exact line _ (elemsLine ty hty) _ ((InT.append _).mpr ⟨v₁, y :: w', rfl, h₁, hy, hw'⟩) hneg

/-- `tuple_empty_arity?/7` answers false on open lines when a size it checks answers false. -/
theorem arity_false (d : Dispatcher) (n m' : Nat) (l : List Term) (ntag : String) (rest S : Term)
    (ok : (Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer n) (.integer m') (Term.list l) rest S =
        .ok (.atom "false")) ∨
      (∃ b : Bool, Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer n) (.integer m') (Term.list l) rest S =
        .ok (boolAtom b)) ∧ ntag = "closed" ∧ l.length ≤ m' + 1 ∧
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open")
          (Term.list (l ++ List.replicate (m' + 1 - l.length) (Term.atom "term"))) rest S = .ok (Term.atom "false")) :
    Elixir.Module.Types.Descr.«tuple_empty_arity?/7» d (.integer n) (.integer m') (.atom "open") (Term.list l)
      (.atom ntag) rest S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
  rcases ok with sizes | ⟨⟨b, sizes⟩, rfl, le, line⟩
  · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, sizes, Lynx.Except.andAlso]
  · have fill := fill_list l (m' + 1) le
    simp only [Int.natCast_add, Int.natCast_one] at fill
    cases b <;> simp [Erlang.erlang.«==/2», Lynx.Except.orElse, sizes, Lynx.Except.andAlso, fill, line, boolAtom]

/-- Tuple lines answer false when a tuple of values of the line escapes their negations. -/
theorem line_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, TupleLit E t) → ∀ (c : Bool) (l : List Term), (∀ e ∈ l, E e) →
      ∀ v, InT den c l v → (∀ N ∈ negs, ¬LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "false") := by
  intro negs
  induction negs with
  | nil => intro _ c l _ v _ _; exact line_nil (D m) _ _ _
  | cons N rest ih =>
    intro lits c l hl v hv hneg
    obtain ⟨k, ntag, nl, rfl, htag, hnl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    have hneg' : ∀ N ∈ rest, ¬LitSem den N v := fun N m => hneg N (List.mem_cons_of_mem _ m)
    have nN : ¬InT den (ntag == "closed") nl v := fun h => hneg _ List.mem_cons_self ⟨k, ntag, nl, rfl, h⟩
    have full := full_of_inT ops sem hS hl hv
    have bools : ∀ (c' : Bool) (l' : List Term), (∀ e ∈ l', Full E K S e) → ∃ b : Bool,
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c' then "closed" else "open")) (Term.list l')
          (Term.list rest) (.map S) = .ok (boolAtom b) := fun c' l' hl' => by
      obtain ⟨b, hb⟩ := line_total ops dops S rest lits' (if c' then "closed" else "open") l' hl'
      exact ⟨b, hb m hm⟩
    rw [list_cons]
    by_cases top : ntag = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact absurd (InT.open_nil v) nN
    by_cases last : c = Bool.false ∧ ntag = "closed" ∧ rest = []
    · obtain ⟨rfl, rfl, rfl⟩ := last
      exact line_last (D m) _ k _ _
    have notLast : ¬((if c then "closed" else "open") = "open" ∧ ntag = "closed" ∧ rest = []) := by
      rintro ⟨hc, h₁, h₂⟩
      cases c
      · exact last ⟨rfl, h₁, h₂⟩
      · simp at hc
    rw [line_cons (D m) _ l k ntag nl rest (.map S) top notLast]
    by_cases skip : ((if c then "closed" else "open") = "closed" ∧ l.length < nl.length) ∨
        (ntag = "closed" ∧ nl.length < l.length)
    · rw [ite_eq_left skip]
      exact ih lits' c l hl v hv hneg'
    rw [ite_eq_right skip]
    have lineFalse := fun (c' : Bool) l' hl' v' hv' hn' => ih lits' c' l' hl' v' hv' hn'
    obtain ⟨be, he⟩ := elements_total ops dops S (.atom (if c then "closed" else "open")) (Term.list rest)
      (fun l' hl' => line_total ops dops S rest lits' _ l' hl') nl hnl [] l (by simp) full
    have heM := he m hm
    simp only [] at heM
    -- how the tuple escapes the negated literal
    rw [InT.iff_open] at nN
    by_cases short : v.length < nl.length
    · -- a shorter tuple: only open lines hold it
      have hc : c = Bool.false := by
        cases c
        · rfl
        · have := hv.closed_length
          exact absurd (Or.inl ⟨rfl, by omega⟩) skip
      subst hc
      have lv := hv.length_le
      have ar := arity_false (D m) l.length nl.length l ntag (Term.list rest) (.map S) (Or.inl
        (sizes_false (D m) l nl.length _ _ (fun i _ _ => bools Bool.true _ (fun e me => by
            simp only [List.mem_append, List.mem_replicate] at me
            rcases me with me | ⟨-, rfl⟩
            · exact full e me
            · exact full_term ops S))
          v.length lv short
          (lineFalse Bool.true _ (fun e me => by
            simp only [List.mem_append, List.mem_replicate] at me
            rcases me with me | ⟨-, rfl⟩
            · exact hl e me
            · exact ops.term) v (inT_fill_closed hv sem.term) hneg') l.length (Nat.le_refl _) lv))
      simp only [Bool.false_eq_true, ite_false] at heM ⊢
      rw [heM, ar]
      cases be <;> rfl
    by_cases escape : InT den Bool.false nl v
    · -- a longer tuple than a closed literal
      have hn : ntag = "closed" := by
        rcases htag with ho | hc
        · exact absurd ⟨escape, fun h => by simp [ho] at h⟩ nN
        · exact hc
      subst hn
      have long : nl.length < v.length := by
        rcases Nat.lt_or_ge nl.length v.length with h | h
        · exact h
        · exact absurd ⟨escape, fun _ => by have := escape.length_le; omega⟩ nN
      have hc : c = Bool.false := by
        cases c
        · rfl
        · have := hv.closed_length
          exact absurd (Or.inr ⟨rfl, by omega⟩) skip
      subst hc
      have le : l.length ≤ nl.length := by
        have : ¬nl.length < l.length := fun h => skip (Or.inr ⟨rfl, h⟩)
        omega
      obtain ⟨bs, hbs⟩ := sizes_total (K := K) S l nl.length (Term.list rest) (fun i _ _ => line_total ops dops S rest
        lits' "closed" _ (fun e me => by
          simp only [List.mem_append, List.mem_replicate] at me
          rcases me with me | ⟨-, rfl⟩
          · exact full e me
          · exact full_term ops S)) l.length (Nat.le_refl _)
      have ar := arity_false (D m) l.length nl.length l "closed" (Term.list rest) (.map S) (Or.inr
        ⟨⟨bs, hbs m hm⟩, rfl, by omega, lineFalse Bool.false _ (fun e me => by
          simp only [List.mem_append, List.mem_replicate] at me
          rcases me with me | ⟨-, rfl⟩
          · exact hl e me
          · exact ops.term) v (inT_fill_open _ hv (by have := hv.length_le; omega) sem.term) hneg'⟩)
      simp only [Bool.false_eq_true, ite_false] at heM ⊢
      rw [heM, ar]
      cases be <;> rfl
    · -- a position where the tuple escapes
      have ef := elements_false ops dops sem hm S hS c rest (fun l' hl' v' hv' hn' => ih lits' c l' hl' v' hv' hn')
        (fun l' hl' => bools c l' hl') nl [] l hnl (by simp) hl (fun hc => by
          subst hc
          have := hv.closed_length
          have : ¬l.length < nl.length := fun h => skip (Or.inl ⟨rfl, h⟩)
          omega) [] v trivial hv (by simpa using hneg') escape (by omega)
      have ef' : Elixir.Module.Types.Descr.«tuple_elements_empty?/6» (D m) .nil
          (.atom (if c then "closed" else "open")) (Term.list l) (Term.list nl) (Term.list rest) (.map S) =
          .ok (.atom "false") := ef
      rw [ef']
      rfl

theorem elements_check2 (ops : ElemOk E K) (S : List (Term × Term)) (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∃ b, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D m) (Term.list l) (.map S) =
      .ok (boolAtom b)) ∧ (b = Bool.true → ∃ e ∈ l, ∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«empty_seen?/2» (D m) e (.map S) = .ok (.atom "true")) := by
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
  refine ⟨l.any res, fun m hm => ?_, fun yes => ?_⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    simp only [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2»]
    refine any_list _ _ _ _ res l fun x mx => ?_
    rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2»]
    exact hres x mx n hn
  · obtain ⟨e, me, he⟩ := List.any_eq_true.mp yes
    exact ⟨e, me, fun m' h => by rw [hres e me m' h, he]; rfl⟩

/-- Checked tuple lines answer false when a tuple of values of the line escapes their negations. -/
theorem line_seen_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) (S : List (Term × Term)) (hS : Safe S) {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (el : ∀ e ∈ l, E e) {negs : List Term} (lits : ∀ t ∈ negs, TupleLit E t) (v : List V)
    (hv : InT den (tag == "closed") l v) (hneg : ∀ N ∈ negs, ¬LitSem den N v) :
    Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4» (D m) (.atom tag) (Term.list l) (Term.list negs) (.map S) =
      .ok (.atom "false") := by
  obtain ⟨b, check, some⟩ := elements_check2 ops S l el
  have full := full_of_inT ops sem hS el hv
  have hb : b = Bool.false := by
    cases b
    · rfl
    · obtain ⟨e, me, he⟩ := some rfl
      have := (full e me).2 m (by omega)
      rw [he m (by omega)] at this
      simp at this
  subst hb
  rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
  simp only [check m hm, Lynx.Except.ok_bind]
  cases negs with
  | nil => simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, Erlang.erlang.«==/2», Term.list]
  | cons N rest =>
    have notNil : Erlang.erlang.«==/2» (Term.list (N :: rest)) .nil = .ok (.atom "false") := by
      simp [Erlang.erlang.«==/2», Term.list, Term.false]
    simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
    have := line_false ops dops sem (by omega : K ≤ m) S hS (N :: rest) lits (tag == "closed") l el v hv hneg
    rcases g with rfl | rfl <;> simpa using this

/-- Tuple BDD walks answer false when a tuple of values along the path, outside the negations, satisfies the BDD. -/
theorem tuple_bdd_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos → (∀ t ∈ negs, TupleLit E t) → ∀ v, InPos den pos v →
      (∀ N ∈ negs, ¬LitSem den N v) → eval (valT E den v) r = Bool.true →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "false") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos →
    (∀ t ∈ negs, TupleLit E t) → ∀ v, InPos den pos v → (∀ N ∈ negs, ¬LitSem den N v) →
      eval (valT E den v) r = Bool.true →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "false"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits v hv hneg _
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    exact line_seen_false ops dops sem hm S hS gt el lits v (inPos_iff.mp hv) hneg
  · intro ok _ pos negs _ _ v _ _ h
    simp at h
  · intro ok k x y okl okLit pos negs hp lits v hv hneg h
    have hl := okLit _ okl
    rw [eval_leaf] at h
    have hlit := (valT_iff sem hl.1).mp h
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_sem ops sem hm hp hl with ⟨_, empty⟩ | ⟨pos', run, hp', sem'⟩
    · exact absurd hlit (empty v hv)
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    simp [run]
    exact line_seen_false ops dops sem hm S hS gt el lits v (inPos_iff.mp ((sem' v).mpr ⟨hv, hlit⟩)) hneg
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits v hv hneg hev
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    have lits' : ∀ t ∈ lit :: negs, TupleLit E t := fun t m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hl.1
      · exact lits t m
    obtain ⟨bd, hbd⟩ := tuple_bdd_total ops dops S hd (fun t ht => (okLit' t ht).1) pos (lit :: negs) hp lits'
    obtain ⟨bu, hbu⟩ := tuple_bdd_total ops dops S hu (fun t ht => (okLit' t ht).1) pos negs hp lits
    have dPart := hbd m hm
    rw [list_cons] at dPart
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    simp only [eval_node] at hev
    rcases inter_sem ops sem hm hp hl with ⟨empty, notLit⟩ | ⟨pos2, run, hp2, sem2⟩
    · -- the literal meets nothing on the path
      have nl : valT E den v lit = Bool.false := by
        cases e : valT E den v lit
        · rfl
        · exact absurd ((valT_iff sem hl.1).mp e) (notLit v hv)
      simp only [nl, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and] at hev
      rcases Bool.or_eq_true_iff.mp hev with hu' | hd'
      · have r := iu okLit' pos negs hp lits v hv hneg hu'
        cases bd <;> simp [empty, dPart, r, Lynx.Except.andAlso, boolAtom]
      · have r := idd okLit' pos (lit :: negs) hp lits' v hv (fun N m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact fun h => by rw [(valT_iff sem hl.1).mpr h] at nl; cases nl
          · exact hneg N m) hd'
        rw [list_cons] at r
        simp [r, Lynx.Except.andAlso]
    obtain ⟨tag2, l2, rfl, gt2, el2⟩ := id hp2
    obtain ⟨bc, hbc⟩ := tuple_bdd_total ops dops S hc (fun t ht => (okLit' t ht).1) _ negs hp2 lits
    have uPart := hbu m hm
    have cPart := hbc m hm
    by_cases hlv : valT E den v lit = Bool.true
    · simp only [hlv, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false] at hev
      rcases Bool.or_eq_true_iff.mp hev with hc' | hu'
      · have r := ic okLit' _ negs hp2 lits v ((sem2 v).mpr ⟨hv, (valT_iff sem hl.1).mp hlv⟩) hneg hc'
        cases bd <;> cases bu <;> simp [run, dPart, r, Lynx.Except.andAlso, boolAtom]
      · have r := iu okLit' pos negs hp lits v hv hneg hu'
        cases bd <;> cases bc <;> simp [run, dPart, cPart, r, Lynx.Except.andAlso, boolAtom]
    · simp only [Bool.not_eq_true] at hlv
      simp only [hlv, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and] at hev
      rcases Bool.or_eq_true_iff.mp hev with hu' | hd'
      · have r := iu okLit' pos negs hp lits v hv hneg hu'
        cases bd <;> cases bc <;> simp [run, dPart, cPart, r, Lynx.Except.andAlso, boolAtom]
      · have r := idd okLit' pos (lit :: negs) hp lits' v hv (fun N m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact fun h => by rw [(valT_iff sem hl.1).mpr h] at hlv; cases hlv
          · exact hneg N m) hd'
        rw [list_cons] at r
        simp [r, Lynx.Except.andAlso]

end

end Elixir.STTDescrProofsTest.Nest
