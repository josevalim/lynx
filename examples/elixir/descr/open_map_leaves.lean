namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

theorem open_leaf_other (d : Dispatcher) (b : Term) (kL : Int) (fo sub : Term)
    (nb : b ≠ .atom "bdd_bot") (nt : b ≠ .atom "bdd_top")
    (nl : ∀ (k : Term) cl, b ≠ .tuple #[k, .atom "closed", cl])
    (nn : ∀ (h k : Term) cl c u d', b ≠ .tuple #[h, .tuple #[k, .atom "closed", cl], c, u, d']) :
    Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
      Elixir.Module.Types.Descr.«bdd_intersection/2» b (.tuple #[.integer kL, .atom "open", fo]) := by
  rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
  split
  · exact absurd rfl nb
  · exact absurd rfl nt
  · exact absurd rfl (nl _ _)
  · exact absurd rfl (nn _ _ _ _ _ _)
  · rfl

theorem open_leaf_inter {Val : (Term → Bool) → Prop} (resp : ∀ ρ, Val ρ → Resp ρ) {ok₁ : Term → Prop} {b L : Term}
    (wb : Bdd ok₁ b) (hL : Bdd ok₁ L) :
    ∃ r', Elixir.Module.Types.Descr.«bdd_intersection/2» b L = .ok r' ∧
      (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P L → Bdd P r') ∧ ∀ ρ, Val ρ → eval ρ r' = (eval ρ b && eval ρ L) := by
  obtain ⟨r', hr, okr, semr⟩ := inter_ok wb hL
  exact ⟨r', hr, fun P sub hP => okr P (wb.mono sub) (hL.mono fun t h => sub t h), fun ρ v => semr ρ (resp ρ v)⟩

theorem eq_cmp (a b : Term) [Decidable (Term.compare (Term.fuel a b) a b = .eq)] :
    Erlang.erlang.«==/2» a b = .ok (.atom (if Term.compare (Term.fuel a b) a b = .eq then "true" else "false")) := by
  by_cases h : Term.compare (Term.fuel a b) a b = .eq <;> simp [Erlang.erlang.«==/2», h, Term.true, Term.false]

theorem open_leaf_ok {Val : (Term → Bool) → Prop} (resp : ∀ ρ, Val ρ → Resp ρ) {ok : Term → Prop} {d : Dispatcher}
    {sub fo : Term} {kL : Int} (hL : ok (.tuple #[.integer kL, .atom "open", fo]))
    (order : ∀ (k : Int) cl, ok (.tuple #[.integer k, .atom "closed", cl]) →
      Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer kL, .atom "open", fo])) (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer kL, .atom "open", fo]) = .lt)
    (spec : ∀ (k : Int) cl, ok (.tuple #[.integer k, .atom "closed", cl]) → ∃ c : Bool,
      d.pure sub #[cl, fo] = .ok (boolAtom c) ∧ (c = Bool.true → ∀ ρ, Val ρ →
        ρ (.tuple #[.integer k, .atom "closed", cl]) = Bool.true → ρ (.tuple #[.integer kL, .atom "open", fo]) = Bool.true)) :
    ∀ ok₁ b, Bdd ok₁ b → (∀ t, ok₁ t → ok t) → ∃ r,
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        .ok r ∧ (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P r) ∧
      ∀ ρ, Val ρ → eval ρ r = (eval ρ b && ρ (.tuple #[.integer kL, .atom "open", fo])) := by
  have wL : ∀ {P : Term → Prop}, P (.tuple #[.integer kL, .atom "open", fo]) →
      Bdd P (.tuple #[.integer kL, .atom "open", fo]) := fun h => Bdd.leaf_iff.mpr h
  have fallback : ∀ {ok₁ : Term → Prop} {b : Term}, Bdd ok₁ b →
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        Elixir.Module.Types.Descr.«bdd_intersection/2» b (.tuple #[.integer kL, .atom "open", fo]) → ∃ r,
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        .ok r ∧ (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P r) ∧
      ∀ ρ, Val ρ → eval ρ r = (eval ρ b && ρ (.tuple #[.integer kL, .atom "open", fo])) := by
    intro ok₁ b wb e
    obtain ⟨r, hr, okr, semr⟩ := open_leaf_inter resp (ok₁ := fun t => ok₁ t ∨ t = .tuple #[.integer kL, .atom "open", fo])
      (wb.mono fun t h => Or.inl h) (wL (Or.inr rfl))
    refine ⟨r, by rw [e, hr], fun P sub hP => okr P (fun t h => h.elim (sub t) (fun e => e ▸ hP)) hP, fun ρ v => ?_⟩
    rw [semr ρ v, eval_leaf]
  refine Bdd.induction (P := fun ok₁ b => (∀ t, ok₁ t → ok t) → ∃ r,
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        .ok r ∧ (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P r) ∧
      ∀ ρ, Val ρ → eval ρ r = (eval ρ b && ρ (.tuple #[.integer kL, .atom "open", fo]))) ?_ ?_ ?_ ?_
  · intro ok₁ _
    refine ⟨_, by rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]; rfl, fun P _ hP => wL hP,
      fun ρ _ => by simp [eval]⟩
  · intro ok₁ _
    refine ⟨_, by rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]; rfl, fun P _ _ => Bdd.bot,
      fun ρ _ => by simp⟩
  · intro ok₁ k x y okl sub₁
    by_cases hx : x = .atom "closed"
    · subst hx
      obtain ⟨c, run, sc⟩ := spec k y (sub₁ _ okl)
      cases c
      · refine fallback (Bdd.leaf_iff.mpr okl) ?_
        rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
        simp [run, isMember, boolAtom]
      · refine ⟨_, ?_, fun P sub _ => Bdd.leaf_iff.mpr (sub _ okl), fun ρ v => ?_⟩
        · rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
          simp [run, isMember, boolAtom]
        · have := sc rfl ρ v
          simp only [eval_leaf]
          revert this
          cases ρ (.tuple #[.integer k, .atom "closed", y]) <;> cases ρ (.tuple #[.integer kL, .atom "open", fo]) <;> simp
    · refine fallback (Bdd.leaf_iff.mpr okl) (open_leaf_other _ _ _ _ _ (by simp) (by simp) (fun k' cl e => ?_)
        (fun h k' cl c u d' e => by simp at e))
      simp at e
      exact hx e.2.1
  · intro ok₁ hh lit c u d' isLeaf okl hc hu hd ic iu id sub₁
    obtain ⟨k, x, y, rfl⟩ := isLeaf
    have w : Bdd ok₁ (.tuple #[.integer hh, .tuple #[.integer k, x, y], c, u, d']) :=
      Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, okl, hc, hu, hd⟩
    by_cases hx : x ≠ .atom "closed"
    · refine fallback w (open_leaf_other _ _ _ _ _ (by simp) (by simp) (fun k' cl e => by simp at e)
        (fun h k' cl c' u' d'' e => ?_))
      simp at e
      exact hx e.2.1.2.1
    have hx' : x = .atom "closed" := Classical.byContradiction hx
    subst hx'
    have sub' : ∀ t, Above ok₁ (.tuple #[.integer k, .atom "closed", y]) t → ok t := fun t ht => sub₁ t ht.1
    have below := order k y (sub₁ _ okl)
    obtain ⟨c₀, run, sc⟩ := spec k y (sub₁ _ okl)
    obtain ⟨nu, hnu, bnu, snu⟩ := iu sub'
    obtain ⟨nd, hnd, bnd, snd⟩ := id sub'
    obtain ⟨nc, hnc, bnc, snc⟩ : ∃ nc, (match c₀ with
        | Bool.true => (Except.ok c : Except Exception Term)
        | Bool.false => Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d c
            (.tuple #[.integer kL, .atom "open", fo]) sub) = .ok nc ∧
        (∀ P : Term → Prop, (∀ t, Above ok₁ (.tuple #[.integer k, .atom "closed", y]) t → P t) →
          P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P nc) ∧
        ∀ ρ, Val ρ → (ρ (.tuple #[.integer k, .atom "closed", y]) && eval ρ nc) =
          (ρ (.tuple #[.integer k, .atom "closed", y]) && eval ρ c && ρ (.tuple #[.integer kL, .atom "open", fo])) := by
      cases c₀
      · obtain ⟨nc, hnc, bnc, snc⟩ := ic sub'
        exact ⟨nc, hnc, bnc, fun ρ v => by rw [snc ρ v, Bool.and_assoc]⟩
      · refine ⟨c, rfl, fun P sub _ => hc.mono sub, fun ρ v => ?_⟩
        have := sc rfl ρ v
        revert this
        cases ρ (.tuple #[.integer k, .atom "closed", y]) <;> cases ρ (.tuple #[.integer kL, .atom "open", fo]) <;>
          cases eval ρ c <;> simp
    have liftA : ∀ {P : Term → Prop}, (∀ t, ok₁ t → P t) →
        ∀ t, Above ok₁ (.tuple #[.integer k, .atom "closed", y]) t → Above P (.tuple #[.integer k, .atom "closed", y]) t :=
      fun sub t ht => ⟨sub t ht.1, ht.2⟩
    have ncOk := bnc (Above ok (.tuple #[.integer k, .atom "closed", y])) (liftA sub₁) ⟨hL, below⟩
    have nuOk := bnu (Above ok (.tuple #[.integer k, .atom "closed", y])) (liftA sub₁) ⟨hL, below⟩
    have ndOk := bnd (Above ok (.tuple #[.integer k, .atom "closed", y])) (liftA sub₁) ⟨hL, below⟩
    have semNode : ∀ ρ, Val ρ →
        eval ρ (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], nc, nu, nd]) =
          (eval ρ (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], c, u, d']) &&
            ρ (.tuple #[.integer kL, .atom "open", fo])) := by
      intro ρ v
      have hc' := snc ρ v
      simp only [eval_node, snu ρ v, snd ρ v]
      revert hc'
      cases ρ (.tuple #[.integer k, .atom "closed", y]) <;> cases ρ (.tuple #[.integer kL, .atom "open", fo]) <;>
        cases eval ρ c <;> cases eval ρ u <;> cases eval ρ d' <;> cases eval ρ nc <;> simp
    have runBlock : Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d
        (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], c, u, d']) (.tuple #[.integer kL, .atom "open", fo])
        sub = (do
          let r ← Lynx.Except.andAlso (Lynx.Except.andAlso (Erlang.erlang.«==/2» nc c) (Erlang.erlang.«==/2» nu u))
            (Erlang.erlang.«==/2» nd d')
          match r with
          | .atom "false" => Elixir.Module.Types.Descr.«bdd_node_new/4» (.tuple #[.integer k, .atom "closed", y]) nc nu nd
          | .atom "true" => pure (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], c, u, d'])
          | r => .error (.error (.tuple #[.atom "case_clause", r]))) := by
      rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
      cases c₀
      · simp only at hnc
        simp [run, isMember, boolAtom, hnc, hnu, hnd]
        rfl
      · simp only [Except.ok.injEq] at hnc
        subst hnc
        simp [run, isMember, boolAtom, hnu, hnd]
        rfl
    classical
    by_cases same : Term.compare (Term.fuel nc c) nc c = .eq ∧ Term.compare (Term.fuel nu u) nu u = .eq ∧ Term.compare (Term.fuel nd d') nd d' = .eq
    · obtain ⟨e₁, e₂, e₃⟩ := same
      refine ⟨_, ?_, fun P sub _ => w.mono sub, fun ρ v => ?_⟩
      · rw [runBlock]; simp [eq_cmp, e₁, e₂, e₃, Lynx.Except.andAlso]
      · rw [← semNode ρ v]
        simp only [eval_node, eval_congr_cmp ncOk (resp ρ v) e₁, eval_congr_cmp nuOk (resp ρ v) e₂,
          eval_congr_cmp ndOk (resp ρ v) e₃]
    · obtain ⟨hn, runn⟩ := node_new (.tuple #[.integer k, .atom "closed", y]) nc nu nd ⟨k, _, y, rfl⟩ ncOk nuOk ndOk
      refine ⟨.tuple #[.integer hn, .tuple #[.integer k, .atom "closed", y], nc, nu, nd], ?_,
        fun P sub hP => Bdd.node_iff.mpr ⟨⟨k, _, y, rfl⟩, sub _ okl, bnc _ (liftA sub)
        ⟨hP, below⟩, bnu _ (liftA sub) ⟨hP, below⟩, bnd _ (liftA sub) ⟨hP, below⟩⟩,
        fun ρ v => by simpa only [eval_node] using semNode ρ v⟩
      rw [runBlock, ← runn]
      by_cases e₁ : Term.compare (Term.fuel nc c) nc c = .eq <;> by_cases e₂ : Term.compare (Term.fuel nu u) nu u = .eq <;>
        by_cases e₃ : Term.compare (Term.fuel nd d') nd d' = .eq
      · exact absurd ⟨e₁, e₂, e₃⟩ same
      all_goals simp [eq_cmp, e₁, e₂, e₃, Lynx.Except.andAlso]

end Elixir.STTDescrProofsTest
