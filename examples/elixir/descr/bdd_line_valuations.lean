namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Lines of BDDs hold what their valuations satisfy. -/

/-- Lines whose positive literals a valuation holds and whose negative literals it does not. -/
def LineSat (ρ : Term → Bool) (line : Term) : Prop :=
  ∃ pos negs : List Term, line = .tuple #[Term.list pos, Term.list negs] ∧ (∀ t ∈ pos, ρ t = Bool.true) ∧
    ∀ t ∈ negs, ρ t = Bool.false

theorem line_inj {a b c d : List Term} (h : Term.tuple #[Term.list a, Term.list b] = .tuple #[Term.list c, Term.list d]) :
    a = c ∧ b = d := by
  simp only [Term.tuple.injEq] at h
  have e₁ : Term.list a = Term.list c := by have := congrArg (fun x : Array Term => x[0]?) h; simpa using this
  have e₂ : Term.list b = Term.list d := by have := congrArg (fun x : Array Term => x[1]?) h; simpa using this
  exact ⟨list_inj e₁, list_inj e₂⟩

/-- Valuations that satisfy a line of a BDD satisfy the BDD. -/
theorem dnf_sat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧
      ∀ l ∈ lines, l ∈ acc ∨ ∀ ρ, LineSat ρ l → (∀ t ∈ pos, ρ t = Bool.true) ∧ (∀ t ∈ negs, ρ t = Bool.false) ∧
        eval ρ r = Bool.true := by
  refine Bdd.induction (P := fun ok r => ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧
      ∀ l ∈ lines, l ∈ acc ∨ ∀ ρ, LineSat ρ l → (∀ t ∈ pos, ρ t = Bool.true) ∧ (∀ t ∈ negs, ρ t = Bool.false) ∧
        eval ρ r = Bool.true) ?_ ?_ ?_ ?_ ok r wr
  · intro ok acc pos negs
    refine ⟨.tuple #[Term.list pos, Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l m => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · refine Or.inr fun ρ ⟨P, N, e, hP, hN⟩ => ?_
      obtain ⟨rfl, rfl⟩ := line_inj e
      exact ⟨hP, hN, by simp⟩
    · exact Or.inl m
  · intro ok acc pos negs
    exact ⟨acc, by simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»], fun l m => Or.inl m⟩
  · intro ok k x y _ acc pos negs
    refine ⟨.tuple #[Term.list (.tuple #[.integer k, x, y] :: pos), Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l m => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · refine Or.inr fun ρ ⟨P, N, e, hP, hN⟩ => ?_
      obtain ⟨rfl, rfl⟩ := line_inj e
      exact ⟨fun t mt => hP t (List.mem_cons_of_mem _ mt), hN, by simp [hP _ List.mem_cons_self]⟩
    · exact Or.inl m
  · intro ok h lit c u d _ _ hc hu hd ic iu id acc pos negs
    obtain ⟨l₁, r₁, h₁⟩ := iu acc pos negs
    obtain ⟨l₂, r₂, h₂⟩ := ic l₁ (lit :: pos) negs
    obtain ⟨l₃, r₃, h₃⟩ := id l₂ pos (lit :: negs)
    refine ⟨l₃, ?_, fun l m => ?_⟩
    · simp only [Term.list] at r₁ r₂ r₃ ⊢
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», r₁, r₂, r₃]
    rcases h₃ l m with m₂ | s₃
    · rcases h₂ l m₂ with m₁ | s₂
      · rcases h₁ l m₁ with m₀ | s₁
        · exact Or.inl m₀
        · refine Or.inr fun ρ sat => ?_
          obtain ⟨p, n, e⟩ := s₁ ρ sat
          exact ⟨p, n, by simp [e]⟩
      · refine Or.inr fun ρ sat => ?_
        obtain ⟨p, n, e⟩ := s₂ ρ sat
        exact ⟨fun t mt => p t (List.mem_cons_of_mem _ mt), n, by simp [p lit List.mem_cons_self, e]⟩
    · refine Or.inr fun ρ sat => ?_
      obtain ⟨p, n, e⟩ := s₃ ρ sat
      exact ⟨p, fun t mt => n t (List.mem_cons_of_mem _ mt), by simp [n lit List.mem_cons_self, e]⟩

/-! Non-empty lists of values: their elements and their tail, which is never a non-empty list. -/

structure LV (V : Type) where
  xs : List V
  last : V

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Lists in a list literal. -/
def LLitSem (den : Term → V → Prop) (lit : Term) (v : LV V) : Prop :=
  ∃ (k : Int) (a b : Term), lit = .tuple #[.integer k, a, b] ∧ (∀ x ∈ v.xs, den a x) ∧ den b v.last

/-- Values that are non-empty lists, and the tail types without their non-empty lists. -/
structure TailSem (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) : Prop where
  unfold : ∀ {e : Term}, E e → ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧
    E e' ∧
    ∀ v, den e' v ↔ den e v ∧ ¬tl v
  witness : ∃ v, ¬tl v

theorem lit_shape {k k' : Int} {a b a' b' : Term} (h : Term.tuple #[.integer k, a, b] = .tuple #[.integer k', a', b']) :
    a = a' ∧ b = b' := by
  simp only [Term.tuple.injEq] at h
  have e₁ := congrArg (fun x : Array Term => x[1]?) h
  have e₂ := congrArg (fun x : Array Term => x[2]?) h
  simp at e₁ e₂
  exact ⟨e₁, e₂⟩

theorem llitSem_iff {k : Int} {a b : Term} {v : LV V} :
    LLitSem den (.tuple #[.integer k, a, b]) v ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last := by
  constructor
  · rintro ⟨k', a', b', e, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := lit_shape e
    exact ⟨h₁, h₂⟩
  · intro h; exact ⟨k, a, b, rfl, h⟩

open Classical in
/-- The valuation of list literals that a list induces, up to comparison. -/
noncomputable def valL (E : Term → Prop) (den : Term → V → Prop) (v : LV V) (t : Term) : Bool :=
  decide (∃ t', compare (fuel t t') t t' = .eq ∧ LLit E t' ∧ LLitSem den t' v)

theorem valL_resp (v : LV V) : Resp (valL E den v) := by
  intro a b h
  simp only [valL]
  congr 1
  apply propext
  constructor
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans h e, rest⟩

theorem valL_iff (sem : ElemSem E K V den Safe) {v : LV V} {t : Term} (ht : LLit E t) :
    valL E den v t = Bool.true ↔ LLitSem den t v := by
  simp only [valL, decide_eq_true_eq]
  constructor
  · rintro ⟨t', e, ⟨k', a', b', rfl, ha', hb'⟩, h⟩
    obtain ⟨k, a, b, rfl, ha, hb⟩ := ht
    rw [llitSem_iff] at h ⊢
    simp only [compare_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
      Ordering.then_eq_eq, List.compareLex_cons_cons] at e
    obtain ⟨-, -, ea, eb, -⟩ := e
    exact ⟨fun x mx => sem.resp ha ha' ea (h.1 x mx), sem.resp hb hb' eb h.2⟩
  · intro h; exact ⟨t, compare_self t, ht, h⟩

/-- Intersecting the positive literals of a line keeps the lists in all of them. -/
theorem lits_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) :
    ∀ (l : List Term), (∀ t ∈ l, LLit E t) → ∀ a b, E a → E b →
      ∃ a' b', E a' ∧ E b' ∧ (∀ m, K + 1 ≤ m →
        Erlang.lists.«foldl_1/3» (D m) litsFun (.tuple #[a, b]) (Term.list l) = .ok (.tuple #[a', b'])) ∧
        ∀ v : LV V, ((∀ x ∈ v.xs, den a' x) ∧ den b' v.last) ↔
          ((∀ x ∈ v.xs, den a x) ∧ den b v.last) ∧ ∀ t ∈ l, LLitSem den t v := by
  intro l
  induction l with
  | nil =>
    intro _ a b ha hb
    exact ⟨a, b, ha, hb, fun m _ => by simp [Erlang.lists.«foldl_1/3»], fun v => by simp⟩
  | cons t rest ih =>
    intro lits a b ha hb
    obtain ⟨k, x, y, rfl, hx, hy⟩ := lits _ List.mem_cons_self
    obtain ⟨a₁, ha₁, ra⟩ := ops.inter ha hx
    obtain ⟨b₁, hb₁, rb⟩ := ops.inter hb hy
    obtain ⟨a', b', ha', hb', run, semr⟩ := ih (fun t m => lits t (List.mem_cons_of_mem _ m)) a₁ b₁ ha₁ hb₁
    have da := sem.inter ha hx (Nat.le_refl K) (ra K (Nat.le_refl K))
    have db := sem.inter hb hy (Nat.le_refl K) (rb K (Nat.le_refl K))
    refine ⟨a', b', ha', hb', fun m hm => ?_, fun v => ?_⟩
    · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [litsFun,
        Erlang.program.«Elixir.Module.Types.Descr:-non_empty_list_literals_intersection/2-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-non_empty_list_literals_intersection/2-fun-0-/2», ra n hn, rb n hn,
        Lynx.Except.ok_bind, pure_bind]
      exact run (n + 1) hm
    · rw [semr v]
      simp only [List.forall_mem_cons, llitSem_iff, da, db]
      constructor
      · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
        exact ⟨⟨fun z mz => (h₁ z mz).1, h₂⟩, ⟨fun z mz => (h₁ z mz).2, h₃⟩, h₄⟩
      · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅⟩
        exact ⟨⟨fun z mz => ⟨h₁ z mz, h₃ z mz⟩, h₂, h₄⟩, h₅⟩

theorem TailSem.ok {tl : V → Prop} (tsem : TailSem E den tl) : TailOk E := fun _ he =>
  let ⟨e', run, he', _⟩ := tsem.unfold he
  ⟨e', run, he'⟩

theorem llitSem_tail {N : Term} {x : V} {xs : List V} {y : V} (h : LLitSem den N ⟨x :: xs, y⟩) :
    LLitSem den N ⟨xs, y⟩ := by
  obtain ⟨k, a, b, e, h₁, h₂⟩ := h
  exact ⟨k, a, b, e, fun z mz => h₁ z (List.mem_cons_of_mem _ mz), h₂⟩

/-- `list_line_negs_empty?/4` finds the lists of a line covered by its negations: negations whose element type
does not hold the line's are skipped, since longer lists escape them. -/
theorem negs_complete (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a : Term} (ha : Full E K S a) :
    ∀ negs : List Term, (∀ t ∈ negs, LLit E t) → ∀ t, Full E K S t → (∀ y, den t y → ¬tl y) →
      (∀ xs : List V, xs ≠ [] → (∀ x ∈ xs, den a x) → ∀ y, den t y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩) →
      ∀ m, K ≤ m → Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list negs) a t (.map S) =
        .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil =>
    intro _ t ht _ H m _
    exfalso
    obtain ⟨x, hx⟩ := full_witness sem hS ha
    obtain ⟨y, hy⟩ := full_witness sem hS ht
    obtain ⟨N, mN, -⟩ := H [x] (by simp) (by simpa using hx) y hy
    simp at mN
  | cons N rest ih =>
    intro lits t ht notl H m hm
    obtain ⟨k, nt, nl, rfl, hnt, hnl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, LLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    obtain ⟨sd, hsd, rsd⟩ := dops.diff ha.1 hnt
    have dsd := sem.diff ha.1 hnt hm (rsd m hm)
    obtain ⟨bs, hbs⟩ := ops.empty hsd S
    cases bs
    · have full : Full E K S sd := ⟨hsd, fun m' h' => by simpa using hbs m' h'⟩
      obtain ⟨w, hw⟩ := full_witness sem hS full
      have hw' := (dsd w).mp hw
      have rc := ih lits' t ht notl (fun xs ne hxs y hy => by
        obtain ⟨N', mN, hN⟩ := H (w :: xs) (by simp) (by simpa [hw'.1] using hxs) y hy
        rcases List.mem_cons.mp mN with rfl | mN
        · exact absurd ((llitSem_iff.mp hN).1 w List.mem_cons_self) hw'.2
        · exact ⟨N', mN, llitSem_tail hN⟩) m hm
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp only [] at rc ⊢
      simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, isMember]
      exact rc
    · obtain ⟨t', ht', ht'E, dt'⟩ := tsem.unfold hnl
      obtain ⟨dd, hdd, rdd⟩ := dops.diff ht.1 ht'E
      have ddd := sem.diff ht.1 ht'E hm (rdd m hm)
      obtain ⟨be, hbe⟩ := ops.empty hdd S
      obtain ⟨b, hb⟩ := negs_total ops dops tsem.ok S ha.1 rest lits' dd hdd
      have h₁ := hb m hm
      dsimp only at h₁
      have last : be = Bool.true ∨ b = Bool.true := by
        cases be
        · right
          have full : Full E K S dd := ⟨hdd, fun m' h' => by simpa using hbe m' h'⟩
          have rc := ih lits' dd full (fun y hy => notl y ((ddd y).mp hy).1) (fun xs ne hxs y hy => by
            have hy' := (ddd y).mp hy
            obtain ⟨N', mN, hN⟩ := H xs ne hxs y hy'.1
            rcases List.mem_cons.mp mN with rfl | mN
            · exact absurd ((dt' y).mpr ⟨(llitSem_iff.mp hN).2, notl y hy'.1⟩) hy'.2
            · exact ⟨N', mN, hN⟩) m hm
          rw [h₁] at rc
          cases b <;> simp_all [boolAtom]
        · exact Or.inl rfl
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp only [] at h₁ ⊢
      simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, isMember,
        ht' m (by have := ops.pos; omega), rdd m hm, hbe m hm, h₁]
      rcases last with rfl | rfl
      · simp
      · cases be <;> simp

/-- Lines of lists are empty when their negations cover them. -/
theorem list_line_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a b : Term} (ha : E a) (hb : E b)
    {negs : List Term} (lits : ∀ t ∈ negs, LLit E t)
    (H : ∀ xs : List V, xs ≠ [] → (∀ x ∈ xs, den a x) → ∀ y, den b y → ¬tl y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩)
    {m : Nat} (hm : K ≤ m) :
    Elixir.Module.Types.Descr.«list_line_empty?/4» (D m) a b (Term.list negs) (.map S) = .ok (.atom "true") := by
  obtain ⟨t, ht, htE, dt⟩ := tsem.unfold hb
  obtain ⟨b₁, h₁⟩ := ops.empty ha S
  obtain ⟨b₂, h₂⟩ := ops.empty htE S
  obtain ⟨b₃, h₃⟩ := negs_total ops dops tsem.ok S ha negs lits t htE
  have e₃ := h₃ m hm
  dsimp only at e₃
  have any : (b₁ || b₂ || b₃) = Bool.true := by
    cases b₁ <;> cases b₂ <;> simp only [Bool.true_or, Bool.or_true, Bool.false_or]
    have fa : Full E K S a := ⟨ha, fun m' h' => by simpa using h₁ m' h'⟩
    have ft : Full E K S t := ⟨htE, fun m' h' => by simpa using h₂ m' h'⟩
    have := negs_complete ops dops sem tsem S hS fa negs lits t ft (fun y hy => ((dt y).mp hy).2)
      (fun xs ne hxs y hy => H xs ne hxs y ((dt y).mp hy).1 ((dt y).mp hy).2) m hm
    rw [e₃] at this
    cases b₃ <;> simp_all [boolAtom]
  unfold Elixir.Module.Types.Descr.«list_line_empty?/4»
  simp only [ht m (by have := ops.pos; omega), Lynx.Except.ok_bind, h₁ m hm, h₂ m hm, e₃, Elixir.STTDescrProofsTest.orElse_bool, any]
  rfl

/-- `non_empty_list_literals_intersection/2` intersects the positive literals of a line, or finds them empty. -/
theorem literals_val (ops : ElemOk E K) (sem : ElemSem E K V den Safe) (S : List (Term × Term)) (pos : List Term)
    (lits : ∀ t ∈ pos, LLit E t) :
    (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m) (Term.list pos)
      (.map S) = .ok (.atom "empty")) ∨
    ∃ a b, E a ∧ E b ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m)
      (Term.list pos) (.map S) = .ok (.tuple #[a, b])) ∧
      ∀ v : LV V, ((∀ x ∈ v.xs, den a x) ∧ den b v.last) ↔ ∀ t ∈ pos, LLitSem den t v := by
  obtain ⟨a, b, ha, hb, fold, semf⟩ := lits_sem ops sem pos lits _ _ ops.term ops.term
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
    simp only [pure_bind, f', Lynx.Except.ok_bind, e₁, e₂, Elixir.STTDescrProofsTest.orElse_bool]
    cases ea <;> cases eb <;> simp [boolAtom, isMember]
  by_cases e : (ea || eb) = Bool.true
  · exact Or.inl fun m hm => by rw [unfold m hm, ite_eq_left e]
  · refine Or.inr ⟨a, b, ha, hb, fun m hm => by rw [unfold m hm, ite_eq_right e], fun v => ?_⟩
    rw [semf v]
    exact ⟨fun h => h.2, fun h => ⟨⟨fun x _ => sem.term x, sem.term _⟩, h⟩⟩

/-- List BDDs that no list satisfies are empty. -/
theorem list_empty_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) {m : Nat} (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (LLit E) r) (S : List (Term × Term))
    (safe : ∀ S', Erlang.maps.«put/3» (.cons (.atom "list") r) (.atom "true") (.map S) = .ok (.map S') → Safe S')
    (unsat : ∀ v : LV V, v.xs ≠ [] → ¬tl v.last → eval (valL E den v) r = Bool.false) :
    Elixir.Module.Types.Descr.«list_empty?/2» (D m) r (.map S) = .ok (.atom "true") := by
  obtain ⟨x₀⟩ := sem.inhabited
  obtain ⟨y₀, hy₀⟩ := tsem.witness
  by_cases top : r = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    have := unsat ⟨[x₀], y₀⟩ (by simp) hy₀
    rw [eval_leaf, (valL_iff sem ⟨_, _, _, rfl, ops.term, ops.term⟩).mpr
      (llitSem_iff.mpr ⟨fun x _ => sem.term x, sem.term _⟩)] at this
    cases this
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 == .eq) = Bool.true
  · unfold Elixir.Module.Types.Descr.«list_empty?/2»
    split
    · exact absurd rfl top
    · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
  have fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 == .eq) = Bool.false := by
    simpa using seen
  obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "list") r) (.atom "true") (.map S) = .ok (.map S') := by
    simp [Erlang.maps.«put/3»]
  have hS' := safe S' put
  obtain ⟨lines, dnf, hlines⟩ := dnf_lines wr (LLit E) (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨lines', dnf', hsat⟩ := dnf_sat wr [] [] []
  have same : lines' = lines := list_inj (by rw [dnf] at dnf'; exact (Except.ok.inj dnf').symm)
  subst same
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
  have each : ∀ x ∈ lines', Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D n) (.map S') x =
      .ok (boolAtom Bool.true) := by
    intro x mx
    obtain ⟨pos, negs, rfl, hp, hn'⟩ := hlines x mx
    rcases literals_val ops sem S' pos hp with empty | ⟨a, b, ha, hb, run, semab⟩
    · simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», empty n hn, boolAtom]
    · have line := list_line_val ops dops sem tsem S' hS' ha hb hn' (m := n) (fun xs ne hxs y hy ny => ?_)
        (by omega)
      · simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», run n hn, line, boolAtom]
      · refine Classical.byContradiction fun none => ?_
        have sat : LineSat (valL E den ⟨xs, y⟩) (.tuple #[Term.list pos, Term.list negs]) :=
          ⟨pos, negs, rfl, fun t mt => (valL_iff sem (hp t mt)).mpr ((semab ⟨xs, y⟩).mp ⟨hxs, hy⟩ t mt),
            fun t mt => by
              cases e : valL E den ⟨xs, y⟩ t
              · rfl
              · exact absurd ⟨t, mt, (valL_iff sem (hn' t mt)).mp e⟩ none⟩
        rcases hsat _ mx with m₀ | s
        · simp at m₀
        · have := (s _ sat).2.2
          rw [unsat ⟨xs, y⟩ ne ny] at this
          cases this
  have all := all_list (D (n + 1)) _ _ _ (fun _ => Bool.true) lines' fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-list_empty?/2-fun-0-/1».pure]
    exact each x mx
  unfold Elixir.Module.Types.Descr.«list_empty?/2»
  split
  · exact absurd rfl top
  · simp only [Term.list] at dnf
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put, Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf]
    rw [all]
    simp [List.all_eq_true, boolAtom]

/-! Lists of basic types. -/

theorem kindName_list {k : Fin 4} (h : k ≠ 1) : kindName k ≠ "list" := by
  obtain ⟨k, lt⟩ := k
  simp only [kindName]
  match k, lt, h with
  | 0, _, _ | 2, _, _ | 3, _, _ => decide
  | 1, _, h => exact absurd rfl h

theorem noList_den (M : List (Term × Term)) (v : FV) :
    denF (.map (noList M)) v ↔ denF (.map M) v ∧ v ≠ .kind 1 := by
  have look : ∀ name, name ≠ "list" → mapLookup (noList M) (.atom name) = mapLookup M (.atom name) := by
    intro name ne
    simp [noList, mapLookup_filter, ne]
  have lookL : mapLookup (noList M) (.atom "list") = Option.none := by simp [noList, mapLookup_filter]
  cases v with
  | bit i => simp [denF, bits, look "bitmap" (by decide)]
  | atom q => simp [denF, amem, look "atom" (by decide)]
  | kind k =>
    by_cases h : k = 1
    · subst h; simp [denF, has, kindName, lookL]
    · simp [denF, has, look _ (kindName_list h), h]

theorem testBit_255 : ∀ i : Fin 8, Nat.testBit 255 i = Bool.true := by decide

theorem tailTerm_den (v : FV) : denF (.map tailTerm) v ↔ v ≠ .kind 1 := by
  cases v with
  | bit i =>
    have b : bits tailTerm = 255 := by simp [bits, tailTerm, mapLookup]
    simp [denF, b, testBit_255]
  | atom q => simp [denF, amem, amemV, tailTerm, mapLookup]
  | kind k =>
    obtain ⟨k, lt⟩ := k
    simp only [denF, has, tailTerm, kindName]
    match k, lt with
    | 0, _ => simp [mapLookup, Fin.ext_iff]
    | 1, _ => simp [mapLookup]
    | 2, _ => simp [mapLookup, Fin.ext_iff]
    | 3, _ => simp [mapLookup, Fin.ext_iff]; decide

def tlF (v : FV) : Prop := v = .kind 1

/-- The top type without lists, whatever order its fields come in, with the lookups of `tailTerm`. -/
theorem tail_term_lookup : ∃ T, (∀ d, Elixir.Module.Types.Descr.«list_tail_unfold/1» d (.atom "term") = .ok (.map T)) ∧
    ∀ q, mapLookup T q = mapLookup tailTerm q := by
  refine ⟨_, fun d => by unfold Elixir.Module.Types.Descr.«list_tail_unfold/1»; rfl, ?_⟩
  refine lookup_tail_perm (fun name => ?_) fun q h => ?_
  · simp only [mapLookup, List.find?, tailTerm, compareExact_eq_atom, Term.atom.injEq]
    all_goals by_cases b : name = "bitmap" <;> by_cases t : name = "tuple" <;> by_cases f : name = "fun" <;>
      by_cases m : name = "map" <;> by_cases a : name = "atom" <;> simp_all
  · by_cases a : ∃ name : String, q = .atom name
    · exact a
    · have na : ∀ k : String, ¬q = .atom k := fun k e => a ⟨k, e⟩
      simp [mapLookup, List.find?, compareExact_eq_atom, na] at h

theorem tailF : TailSem LElem denF tlF := by
  refine ⟨fun {e} he => ?_, ⟨.bit 0, by simp [tlF]⟩⟩
  rcases he with rfl | ⟨M, rfl, bM⟩
  · obtain ⟨T, run, look⟩ := tail_term_lookup
    have den : ∀ v, denF (.map T) v ↔ denF (.map tailTerm) v := fun v => by
      cases v <;> simp [denF, bits, amem, has, look]
    exact ⟨.map T, fun m _ => run (D m), Or.inr ⟨T, rfl, basic_of_lookup look⟩,
      fun v => by simp [denF_term, den, tailTerm_den, tlF]⟩
  · exact ⟨_, fun m _ => tail_map (D m) M, Or.inr ⟨_, rfl, bM.noList⟩, fun v => by simp [noList_den, tlF]⟩

end Elixir.STTDescrProofsTest
