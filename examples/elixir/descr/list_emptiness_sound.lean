namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Soundness of list emptiness: `list_empty?/2` answers `true` only for list types without lists of values. -/

/-- A valuation satisfying a BDD satisfies one of its lines. -/
theorem nl_dnf_cover {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧ (∀ l ∈ acc, l ∈ lines) ∧
      ∀ ρ, (∀ t ∈ pos, ρ t = Bool.true) → (∀ t ∈ negs, ρ t = Bool.false) → eval ρ r = Bool.true →
        ∃ l ∈ lines, LineSat ρ l := by
  refine Bdd.induction (P := fun ok r => ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧ (∀ l ∈ acc, l ∈ lines) ∧
      ∀ ρ, (∀ t ∈ pos, ρ t = Bool.true) → (∀ t ∈ negs, ρ t = Bool.false) → eval ρ r = Bool.true →
        ∃ l ∈ lines, LineSat ρ l) ?_ ?_ ?_ ?_ ok r wr
  · intro ok acc pos negs
    refine ⟨.tuple #[Term.list pos, Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l ml => List.mem_cons_of_mem _ ml,
      fun ρ hp hn _ => ?_⟩
    exact ⟨_, List.mem_cons_self, pos, negs, rfl, hp, hn⟩
  · intro ok acc pos negs
    exact ⟨acc, by simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»], fun l ml => ml, fun ρ _ _ h => by simp at h⟩
  · intro ok k x y _ acc pos negs
    refine ⟨.tuple #[Term.list (.tuple #[.integer k, x, y] :: pos), Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l ml => List.mem_cons_of_mem _ ml,
      fun ρ hp hn h => ?_⟩
    refine ⟨_, List.mem_cons_self, _, negs, rfl, fun t mt => ?_, hn⟩
    rcases List.mem_cons.mp mt with rfl | mt
    · simpa using h
    · exact hp t mt
  · intro ok h lit c u d _ _ hc hu hd ic iu id acc pos negs
    obtain ⟨l₁, r₁, a₁, h₁⟩ := iu acc pos negs
    obtain ⟨l₂, r₂, a₂, h₂⟩ := ic l₁ (lit :: pos) negs
    obtain ⟨l₃, r₃, a₃, h₃⟩ := id l₂ pos (lit :: negs)
    refine ⟨l₃, ?_, fun l ml => a₃ l (a₂ l (a₁ l ml)), fun ρ hp hn e => ?_⟩
    · simp only [Term.list] at r₁ r₂ r₃ ⊢
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», r₁, r₂, r₃]
    simp only [eval_node] at e
    cases hu' : eval ρ u
    · cases hl : ρ lit
      · simp [hl, hu'] at e
        obtain ⟨l, ml, sl⟩ := h₃ ρ hp (fun t mt => by
          rcases List.mem_cons.mp mt with rfl | mt
          · exact hl
          · exact hn t mt) e
        exact ⟨l, ml, sl⟩
      · simp [hl, hu'] at e
        obtain ⟨l, ml, sl⟩ := h₂ ρ (fun t mt => by
          rcases List.mem_cons.mp mt with rfl | mt
          · exact hl
          · exact hp t mt) hn e
        exact ⟨l, a₃ l ml, sl⟩
    · obtain ⟨l, ml, sl⟩ := h₁ ρ hp hn hu'
      exact ⟨l, a₃ l (a₂ l ml), sl⟩

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- `list_line_negs_empty?/4` answers `true` only when its negations cover the lists of the line. -/
theorem nl_negs_sound (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a : Term} (ha : E a) :
    ∀ negs : List Term, (∀ t ∈ negs, LLit E t) → ∀ t, E t → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list negs) a t (.map S) = .ok (.atom "true") →
      ∀ xs : List V, (∀ x ∈ xs, den a x) → ∀ y, den t y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩ := by
  intro negs
  induction negs with
  | nil =>
    intro _ t _ m _ run
    rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def] at run
    simp at run
  | cons N rest ih =>
    intro lits t ht m hm run xs hxs y hy
    obtain ⟨k, nt, nl, rfl, hnt, hnl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, LLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    obtain ⟨sd, hsd, rsd⟩ := dops.diff ha hnt
    have dsd := sem.diff ha hnt hm (rsd m hm)
    obtain ⟨bs, hbs⟩ := ops.empty hsd S
    cases bs
    · have rc : Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list rest) a t (.map S) =
          .ok (.atom "true") := by
        rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def] at run
        simp only [] at run ⊢
        simpa [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, Lynx.Except.guard,
          isMember] using run
      obtain ⟨N', mN, hN⟩ := ih lits' t ht m hm rc xs hxs y hy
      exact ⟨N', List.mem_cons_of_mem _ mN, hN⟩
    · have sub : ∀ x, den a x → den nt x := fun x hx => Classical.byContradiction fun nx =>
        (sem.empty hsd hS hm (hbs m hm)).mp rfl x ((dsd x).mpr ⟨hx, nx⟩)
      have cover : den nl y → ∃ N' ∈ Term.tuple #[.integer k, nt, nl] :: rest, LLitSem den N' ⟨xs, y⟩ :=
        fun h => ⟨_, List.mem_cons_self, llitSem_iff.mpr ⟨fun x mx => sub x (hxs x mx), h⟩⟩
      obtain ⟨t', ht', ht'E, dt'⟩ := tsem.unfold hnl
      obtain ⟨dd, hdd, rdd⟩ := dops.diff ht ht'E
      have ddd := sem.diff ht ht'E hm (rdd m hm)
      obtain ⟨be, hbe⟩ := ops.empty hdd S
      obtain ⟨b, hb⟩ := negs_total ops dops tsem.ok S ha rest lits' dd hdd
      have h₁ := hb m hm
      dsimp only at h₁
      have res : (be || b) = Bool.true := by
        rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def] at run
        simp only [] at h₁ run
        simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, isMember,
          ht' m (by have := ops.pos; omega), rdd m hm, hbe m hm, h₁] at run
        cases be <;> cases b <;> simp_all
      by_cases hn : den nl y
      · exact cover hn
      have hd : den dd y := (ddd y).mpr ⟨hy, fun h => hn ((dt' y).mp h).1⟩
      cases be
      · simp only [Bool.false_or] at res
        subst res
        obtain ⟨N', mN, hN⟩ := ih lits' dd hdd m hm h₁ xs hxs y hd
        exact ⟨N', List.mem_cons_of_mem _ mN, hN⟩
      · exact absurd hd ((sem.empty hdd hS hm (hbe m hm)).mp rfl y)

/-- `list_line_empty?/4` answers `true` only when the negations cover the lists of the line. -/
theorem nl_line_sound (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a b : Term} (ha : E a) (hb : E b)
    {negs : List Term} (lits : ∀ t ∈ negs, LLit E t) {m : Nat} (hm : K ≤ m)
    (run : Elixir.Module.Types.Descr.«list_line_empty?/4» (D m) a b (Term.list negs) (.map S) = .ok (.atom "true")) :
    ∀ xs : List V, xs ≠ [] → (∀ x ∈ xs, den a x) → ∀ y, den b y → ¬tl y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩ := by
  intro xs ne hxs y hy ny
  obtain ⟨t, ht, htE, dt⟩ := tsem.unfold hb
  obtain ⟨b₁, h₁⟩ := ops.empty ha S
  obtain ⟨b₂, h₂⟩ := ops.empty htE S
  obtain ⟨b₃, h₃⟩ := negs_total ops dops tsem.ok S ha negs lits t htE
  have e₃ := h₃ m hm
  dsimp only at e₃
  have res : (b₁ || b₂ || b₃) = Bool.true := by
    unfold Elixir.Module.Types.Descr.«list_line_empty?/4» at run
    simp only [ht m (by have := ops.pos; omega), Lynx.Except.ok_bind, h₁ m hm, h₂ m hm, e₃, Elixir.STTDescrProofsTest.orElse_bool] at run
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp_all [boolAtom]
  have hyt : den t y := (dt y).mpr ⟨hy, ny⟩
  cases b₁
  · cases b₂
    · simp only [Bool.false_or] at res
      subst res
      exact nl_negs_sound ops dops sem tsem S hS ha negs lits t htE m hm e₃ xs hxs y hyt
    · exact absurd hyt ((sem.empty htE hS hm (h₂ m hm)).mp rfl y)
  · obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil xs ne
    exact absurd (hxs x mx) ((sem.empty ha hS hm (h₁ m hm)).mp rfl x)

/-- `non_empty_list_literals_intersection/2` finds the positive literals of a line empty only when no list is in all
of them. -/
theorem nl_literals_sound (ops : ElemOk E K) (sem : ElemSem E K V den Safe) (S : List (Term × Term)) (hS : Safe S)
    (pos : List Term) (lits : ∀ t ∈ pos, LLit E t) :
    ((∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m) (Term.list pos)
      (.map S) = .ok (.atom "empty")) ∧ ∀ v : LV V, v.xs ≠ [] → ¬∀ t ∈ pos, LLitSem den t v) ∨
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
  have semf' : ∀ v : LV V, ((∀ x ∈ v.xs, den a x) ∧ den b v.last) ↔ ∀ t ∈ pos, LLitSem den t v := fun v => by
    rw [semf v]
    exact ⟨fun h => h.2, fun h => ⟨⟨fun x _ => sem.term x, sem.term _⟩, h⟩⟩
  by_cases e : (ea || eb) = Bool.true
  · refine Or.inl ⟨fun m hm => by rw [unfold m hm, ite_eq_left e], fun v ne all => ?_⟩
    obtain ⟨hxs, hlast⟩ := (semf' v).mpr all
    cases ea
    · simp only [Bool.false_or] at e
      subst e
      exact (sem.empty hb hS (Nat.le_refl K) (heb K (Nat.le_refl K))).mp rfl _ hlast
    · obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil v.xs ne
      exact (sem.empty ha hS (Nat.le_refl K) (hea K (Nat.le_refl K))).mp rfl x (hxs x mx)
  · exact Or.inr ⟨a, b, ha, hb, fun m hm => by rw [unfold m hm, ite_eq_right e], semf'⟩

/-- `list_empty?/2` answers `true` only for list BDDs that no list of values satisfies, when the BDD is not seen
and the seen set with it keeps the emptiness of elements exact. -/
theorem nl_list_sound (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) {m : Nat} (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (LLit E) r) (S : List (Term × Term))
    (fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 == .eq) = Bool.false)
    (safe : Safe ((.cons (.atom "list") r, .atom "true") :: S))
    (run : Elixir.Module.Types.Descr.«list_empty?/2» (D m) r (.map S) = .ok (.atom "true")) :
    ∀ v : LV V, v.xs ≠ [] → ¬tl v.last → eval (valL E den v) r = Bool.false := by
  by_cases top : r = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    unfold Elixir.Module.Types.Descr.«list_empty?/2» at run
    simp at run
  have put : Erlang.maps.«put/3» (.cons (.atom "list") r) (.atom "true") (.map S) =
      .ok (.map ((.cons (.atom "list") r, .atom "true") :: S)) := rfl
  generalize hS' : (Term.cons (.atom "list") r, Term.atom "true") :: S = S' at safe put
  obtain ⟨lines, dnf, hlines⟩ := dnf_lines wr (LLit E) (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨lines', dnf', -, hcov⟩ := nl_dnf_cover wr [] [] []
  have same : lines' = lines := list_inj (by rw [dnf] at dnf'; exact (Except.ok.inj dnf').symm)
  subst same
  have each : ∀ x ∈ lines', ∃ bx, (∀ m', K + 1 ≤ m' →
      Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D m') (.map S') x = .ok (boolAtom bx)) ∧
      (bx = Bool.true → ∀ v : LV V, v.xs ≠ [] → ¬tl v.last → ¬LineSat (valL E den v) x) := by
    intro x mx
    obtain ⟨pos, negs, rfl, hp, hn⟩ := hlines x mx
    rcases nl_literals_sound ops sem S' safe pos hp with ⟨empty, none⟩ | ⟨a, b, ha, hb, runl, semab⟩
    · refine ⟨Bool.true, fun m' h => by
        simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», empty m' h, boolAtom], fun _ v ne _ sat => ?_⟩
      obtain ⟨P, N, e, hP, -⟩ := sat
      obtain ⟨rfl, rfl⟩ := line_inj e
      exact none v ne fun t mt => (valL_iff sem (hp t mt)).mp (hP t mt)
    · obtain ⟨bl, hbl⟩ := line_list_total ops dops tsem.ok S' ha hb hn
      refine ⟨bl, fun m' h => by
        have := hbl m' (by omega)
        dsimp only at this
        simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», runl m' h, this], fun e v ne nl sat => ?_⟩
      subst e
      obtain ⟨P, N, ee, hP, hN⟩ := sat
      obtain ⟨rfl, rfl⟩ := line_inj ee
      obtain ⟨hxs, hlast⟩ := (semab v).mpr fun t mt => (valL_iff sem (hp t mt)).mp (hP t mt)
      have line := hbl K (Nat.le_refl K)
      dsimp only at line
      obtain ⟨N', mN, hN'⟩ := nl_line_sound ops dops sem tsem S' safe ha hb hn (Nat.le_refl K)
        (by simpa [boolAtom] using line) v.xs ne hxs v.last hlast nl
      have := hN N' mN
      rw [(valL_iff sem (hn N' mN)).mpr hN'] at this
      cases this
  classical
  let res : Term → Bool := fun x => if h : x ∈ lines' then Classical.choose (each x h) else Bool.false
  have hres : ∀ x (h : x ∈ lines'), ∀ m', K + 1 ≤ m' →
      Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D m') (.map S') x = .ok (boolAtom (res x)) := by
    intro x mx m' h
    simp only [res, dite_eq_left mx]
    exact (Classical.choose_spec (each x mx)).1 m' h
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
  have all := all_list (D (n + 1)) _ _ _ res lines' fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-list_empty?/2-fun-0-/1».pure]
    exact hres x mx n hn
  have allTrue : lines'.all res = Bool.true := by
    unfold Elixir.Module.Types.Descr.«list_empty?/2» at run
    split at run
    · exact absurd rfl top
    · simp only [Term.list] at dnf
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
        Term.false, put, Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf] at run
      rw [all] at run
      cases h : lines'.all res
      · rw [h] at run; simp [boolAtom] at run
      · rfl
  intro v ne nl
  cases e : eval (valL E den v) r
  · rfl
  · obtain ⟨l, ml, sat⟩ := hcov _ (by simp) (by simp) e
    have rl : res l = Bool.true := List.all_eq_true.mp allTrue l ml
    have := (Classical.choose_spec (each l ml)).2
    simp only [res, dite_eq_left ml] at rl
    exact absurd sat (this rl v ne nl)

end

end Elixir.STTDescrProofsTest.Nest
