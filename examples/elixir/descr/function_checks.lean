namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! What the function checks compute: applications of arrows to domains, and the shortcuts of `phi_starter/4`. -/

/-- A proposition as a Boolean. -/
noncomputable def bp (p : Prop) : Bool := @decide p (Classical.propDecidable p)

@[simp] theorem bp_true {p : Prop} : bp p = Bool.true ↔ p := by simp [bp]
@[simp] theorem bp_false {p : Prop} : bp p = Bool.false ↔ ¬p := by simp [bp]

theorem bp_congr {p q : Prop} (h : p ↔ q) : bp p = bp q := by
  rw [propext h]

section
variable {V : Type}

/-- Element types for the function checks under the seen set `seen`: closed under the operations the checks
perform, with exact emptiness under `seen` and exact subtyping, and sound disjointness, from call depth `K`. -/
structure FunElem (E : Term → Prop) (den : Term → V → Prop) (K : Nat) (seen : Term) : Prop where
  phi : PhiCtx E den K seen
  union : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∨ den b v
  neg : ∀ {a}, E a → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c) ∧
    ∀ v, den c v ↔ ¬den a v
  sub : ∀ {a b}, E a → E b → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom (bp (∀ v, den a v → den b v)))
  disj : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v → False)
  term : E (.atom "term") ∧ ∀ v, den (.atom "term") v
  none : E (.map []) ∧ ∀ v, ¬den (.map []) v

/-- Domains of arrows, tuple types of their arguments standing for lists of values `dden`: closed under the
operations the checks perform, with exact emptiness with no seen set and under `seen`, from call depth `K`. -/
structure FunDom (Dm E : Term → Prop) (den : Term → V → Prop) (dden : Term → List V → Prop) (K : Nat)
    (seen : Term) : Prop where
  dom : ∀ l : List Term, (∀ a ∈ l, E a) → ∃ t, Dm t ∧ Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) = .ok t ∧
    ∀ x, dden t x ↔ FunSem.InDomR (l.map den) x
  none : Dm (.map []) ∧ ∀ x, ¬dden (.map []) x
  isMap : ∀ {a}, Dm a → ∃ X, a = .map X
  union : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧ ∀ x, dden c x ↔ dden a x ∨ dden b x
  inter : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    ∀ x, dden c x ↔ dden a x ∧ dden b x
  diff : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    ∀ x, dden c x ↔ dden a x ∧ ¬dden b x
  empty : ∀ {a}, Dm a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map []) = .ok (boolAtom (bp (∀ x, ¬dden a x)))
  emptySeen : ∀ {a}, Dm a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a seen = .ok (boolAtom (bp (∀ x, ¬dden a x)))

variable {E Dm : Term → Prop} {den : Term → V → Prop} {dden : Term → List V → Prop} {K : Nat} {seen : Term}

theorem FunDom.empty1 (fd : FunDom Dm E den dden K seen) {a : Term} (ha : Dm a) (m : Nat) (hm : K ≤ m) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (bp (∀ x, ¬dden a x))) := by
  obtain ⟨X, rfl⟩ := fd.isMap ha
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  exact fd.empty ha m hm

theorem app_congr_I {I I' : List V → Prop} (h : ∀ x, I x ↔ I' x) (r : V → Prop) (P : List (FunSem.Arrow V)) (v : V) :
    FunSem.App I r P v ↔ FunSem.App I' r P v := by
  have : I = I' := funext fun x => propext (h x)
  rw [this]

theorem app_congr_r (I : List V → Prop) {r r' : V → Prop} (h : ∀ v, r v ↔ r' v) (P : List (FunSem.Arrow V)) (v : V) :
    FunSem.App I r P v ↔ FunSem.App I r' P v := by
  have : r = r' := funext fun x => propext (h x)
  rw [this]

/-- `aux_apply/4` unites its result with the application of the arrows to the input, refined by the returns
reached so far. -/
theorem aux_apply_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) :
    ∀ P : List (Term × List Term × Term), PosOk E n P → ∀ result input rets, E result → Dm input → E rets →
      ∃ r, E r ∧ (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«aux_apply/4» (D m) result input rets (encP P) = .ok r) ∧
        ∀ v, den r v ↔ den result v ∨ FunSem.App (dden input) (den rets) (semP den P) v := by
  intro P
  induction P with
  | nil =>
    intro _ result input rets hres _ hrets
    obtain ⟨u, hu, ru, su⟩ := fe.union hres hrets
    by_cases hs : ∀ v, den rets v → den result v
    · refine ⟨result, hres, fun m hm => ?_, fun v => ?_⟩
      · have h := fe.sub hrets hres m hm
        have hb : bp (∀ v, den rets v → den result v) = Bool.true := bp_true.mpr hs
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [encP, Term.list, h, hb, isMember]
      · simp only [semP, List.map_nil, FunSem.App]
        exact ⟨Or.inl, fun h => h.elim id (hs v)⟩
    · refine ⟨u, hu, fun m hm => ?_, fun v => ?_⟩
      · have h := fe.sub hrets hres m hm
        have hb : bp (∀ v, den rets v → den result v) = Bool.false := bp_false.mpr hs
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [encP, Term.list, h, hb, isMember, ru m hm]
      · simp only [semP, List.map_nil, FunSem.App]
        exact su v
  | cons p rest ih =>
    intro hP result input rets hres hin hrets
    obtain ⟨key, args, ret⟩ := p
    obtain ⟨hargs, hret, -⟩ := hP _ List.mem_cons_self
    have ih' := ih fun q mq => hP q (List.mem_cons_of_mem _ mq)
    obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom args hargs
    obtain ⟨sub, hsub, rsub, ssub⟩ := fd.diff hin hdom
    obtain ⟨refine, hrefine, rrefine, srefine⟩ := fe.phi.inter hrets hret
    have es := fd.empty1 hsub
    have app : ∀ v, FunSem.App (dden input) (den rets) (semP den ((key, args, ret) :: rest)) v ↔
        ((∃ x, dden sub x) ∧ FunSem.App (dden sub) (den rets) (semP den rest) v) ∨
          FunSem.App (dden input) (den refine) (semP den rest) v := by
      intro v
      simp only [semP, List.map_cons, FunSem.App]
      have e₁ : ∀ x, dden sub x ↔ dden input x ∧ ¬FunSem.InDomR (args.map den) x := fun x => by
        rw [ssub, sdom]
      refine or_congr (and_congr ⟨fun ⟨x, h⟩ => ⟨x, (e₁ x).mpr h⟩, fun ⟨x, h⟩ => ⟨x, (e₁ x).mp h⟩⟩
        (app_congr_I (fun x => (e₁ x).symm) _ _ v)) (app_congr_r _ (fun v => (srefine v).symm) _ v)
    by_cases ne : ∃ x, dden sub x
    · have hb : bp (∀ x, ¬dden sub x) = Bool.false := bp_false.mpr fun h => by
        obtain ⟨x, hx⟩ := ne; exact h x hx
      obtain ⟨r₁, hr₁, run₁, s₁⟩ := ih' result sub rets hres hsub hrets
      obtain ⟨r, hr, run, s⟩ := ih' r₁ input refine hr₁ hin hrefine
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp only [encP, List.map_cons, Term.list] at run₁ run ⊢
        simp [rdom, rsub m hm, rrefine m hm, es m hm, hb, isMember, run₁ m hm, run m hm]
      · rw [s, s₁, app]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨ne, h⟩)
          · exact Or.inr (Or.inr h)
        · rintro (h | ⟨_, h⟩ | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
    · have hb : bp (∀ x, ¬dden sub x) = Bool.true := bp_true.mpr fun x hx => ne ⟨x, hx⟩
      obtain ⟨r, hr, run, s⟩ := ih' result input refine hres hin hrefine
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp only [encP, List.map_cons, Term.list] at run ⊢
        simp [rdom, rsub m hm, rrefine m hm, es m hm, hb, isMember, run m hm]
      · rw [s, app]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | ⟨h, _⟩ | h)
          · exact Or.inl h
          · exact absurd h ne
          · exact Or.inr h

/-- Folds that unite into their accumulator, at every call depth from `K`. -/
theorem foldl1_or {W : Type} (K : Nat) (f : Term) (Inv : Term → Prop) (sem : Term → W → Prop) (G : Term → W → Prop) :
    ∀ l : List Term, (∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ (∀ m, K ≤ m → (D m).pure f #[x, a] = .ok a') ∧
      ∀ w, sem a' w ↔ sem a w ∨ G x w) →
      ∀ acc, Inv acc → ∃ r, Inv r ∧ (∀ m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list l) = .ok r) ∧
        ∀ w, sem r w ↔ sem acc w ∨ ∃ x ∈ l, G x w := by
  intro l
  induction l with
  | nil => exact fun _ acc h => ⟨acc, h, fun m _ => by simp [Erlang.lists.«foldl_1/3»], fun w => by simp⟩
  | cons x xs ih =>
    intro step acc hacc
    obtain ⟨a', ha', run, s'⟩ := step x List.mem_cons_self acc hacc
    obtain ⟨r, hr, rest, s⟩ := ih (fun y my => step y (List.mem_cons_of_mem _ my)) a' ha'
    refine ⟨r, hr, fun m hm => ?_, fun w => ?_⟩
    · rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [run m hm, Lynx.Except.ok_bind]
      exact rest m hm
    · rw [s, s']
      constructor
      · rintro ((h | h) | ⟨y, my, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, h⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ my, h⟩
      · rintro (h | ⟨y, my, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp my with rfl | my
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨y, my, h⟩

theorem foldl_or {W : Type} (K : Nat) (mo nm : String) (caps : Array Term) (Inv : Term → Prop) (sem : Term → W → Prop)
    (G : Term → W → Prop) (l : List Term)
    (step : ∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ (∀ m, K ≤ m → (D m).pure (.function mo nm 2 caps) #[x, a] = .ok a') ∧
      ∀ w, sem a' w ↔ sem a w ∨ G x w) (acc : Term) (hacc : Inv acc) :
    ∃ r, Inv r ∧ (∀ m, K ≤ m →
      Erlang.lists.«foldl/3» (D m) (.function mo nm 2 caps) acc (Term.list l) = .ok r) ∧
      ∀ w, sem r w ↔ sem acc w ∨ ∃ x ∈ l, G x w := by
  obtain ⟨r, hr, run, s⟩ := foldl1_or K _ Inv sem G l step acc hacc
  refine ⟨r, hr, fun m hm => ?_, s⟩
  have := run m hm
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using this
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem enc_inj {a b a' b' : Term} {l l' : List Term}
    (e : Term.tuple #[a, Term.list l, b] = .tuple #[a', Term.list l', b']) : a = a' ∧ l = l' ∧ b = b' := by
  simp only [Term.tuple.injEq] at e
  have e₀ := congrArg (fun a : Array Term => a[0]?) e
  have e₁ := congrArg (fun a : Array Term => a[1]?) e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₀ e₁ e₂
  exact ⟨e₀, list_inj e₁, e₂⟩

/-- `fetch_domain/1` unites the domains of the positive arrows. -/
theorem fetch_domain_sem (fd : FunDom Dm E den dden K seen) (n : Nat) (P : List (Term × List Term × Term))
    (hP : PosOk E n P) :
    ∃ fdom, Dm fdom ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«fetch_domain/1» (D m) (encP P) = .ok fdom) ∧
      ∀ x, dden fdom x ↔ ∃ p ∈ semP den P, FunSem.InDomR p.1 x := by
  let G : Term → List V → Prop := fun t x => ∃ p ∈ P, t = .tuple #[p.1, Term.list p.2.1, p.2.2] ∧
    FunSem.InDomR (p.2.1.map den) x
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fetch_domain/1-fun-0-" #[] Dm dden G
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (by
      intro t mt a ha
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs, -, -⟩ := hP p mp
      obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom p.2.1 hargs
      obtain ⟨u, hu, ru, su⟩ := fd.union ha hdom
      refine ⟨u, hu, fun m hm => ?_, fun x => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fetch_domain/1-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-fetch_domain/1-fun-0-/2», rdom, ru m' hm']
      · rw [su, sdom]
        refine or_congr Iff.rfl ⟨fun h => ⟨p, mp, rfl, h⟩, fun ⟨q, mq, e, h⟩ => ?_⟩
        obtain ⟨-, el, -⟩ := enc_inj e
        rw [el]; exact h) (.map []) fd.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fetch_domain/1»; exact run m hm, fun x => ?_⟩
  rw [s]
  simp only [fd.none.2, false_or, List.mem_map, semP, G]
  constructor
  · rintro ⟨_, ⟨p, mp, rfl⟩, q, mq, e, h⟩
    exact ⟨_, ⟨q, mq, rfl⟩, h⟩
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, p, mp, rfl, h⟩

/-- `fun_apply_static/2` applies the positive arrows to the domain of the arguments. -/
theorem apply_static_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«fun_apply_static/2» (D m) (Term.list args) (Term.list [encP P]) = .ok r) ∧
      ∀ v, den r v ↔ FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den P) v := by
  obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom args hargs
  let G : Term → V → Prop := fun t v => t = encP P ∧ FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den P) v
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fun_apply_static/2-fun-0-" #[dom] E den G
    [encP P] (by
      intro t mt a ha
      rw [List.mem_singleton.mp mt]
      obtain ⟨r, hr, run, s⟩ := aux_apply_sem fe fd n P hP a dom (.atom "term") ha hdom fe.term.1
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_static/2-fun-0-/2».pure]
        exact run m' hm'
      · rw [s, app_congr_I sdom, app_congr_r _ (fun v => iff_true_intro (fe.term.2 v))]
        simp [G]) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fun_apply_static/2»; simp [rdom, run m hm],
    fun v => ?_⟩
  rw [s]
  simp [fe.none.2, G]

/-- `apply_disjoint/2` unites the returns of the positive arrows whose domain meets the arguments. -/
theorem apply_disjoint_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«apply_disjoint/2» (D m) (Term.list args) (encP P) = .ok r) ∧
      ∀ v, den r v ↔ ∃ p ∈ semP den P, (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR p.1 x) ∧ p.2 v := by
  obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom args hargs
  let G : Term → V → Prop := fun t v => ∃ p ∈ P, t = .tuple #[p.1, Term.list p.2.1, p.2.2] ∧
    (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x) ∧ den p.2.2 v
  have G_enc : ∀ p ∈ P, ∀ v, G (.tuple #[p.1, Term.list p.2.1, p.2.2]) v ↔
      (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x) ∧ den p.2.2 v := by
    intro p mp v
    constructor
    · rintro ⟨q, mq, e, h⟩
      obtain ⟨-, el, er⟩ := enc_inj e
      rw [el, er]; exact h
    · exact fun h => ⟨p, mp, rfl, h⟩
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-apply_disjoint/2-fun-0-" #[dom] E den G
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (by
      intro t mt a ha
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs', hret', -⟩ := hP p mp
      obtain ⟨dom', hdom', rdom', sdom'⟩ := fd.dom p.2.1 hargs'
      obtain ⟨i, hi, ri, si⟩ := fd.inter hdom' hdom
      have ei := fd.empty1 hi
      obtain ⟨u, hu, ru, su⟩ := fe.union ha hret'
      by_cases meet : ∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x
      · have hb : bp (∀ x, ¬dden i x) = Bool.false := bp_false.mpr fun h => by
          obtain ⟨x, h₁, h₂⟩ := meet
          exact h x ((si x).mpr ⟨(sdom' x).mpr h₂, (sdom x).mpr h₁⟩)
        refine ⟨u, hu, fun m hm => ?_, fun v => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
          simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm', ei m' hm', hb,
            isMember, ru m' hm']
        · rw [su, G_enc p mp]
          exact or_congr Iff.rfl ⟨fun h => ⟨meet, h⟩, fun h => h.2⟩
      · have hb : bp (∀ x, ¬dden i x) = Bool.true := bp_true.mpr fun x hx => by
          rw [si, sdom, sdom'] at hx
          exact meet ⟨x, hx.2, hx.1⟩
        refine ⟨a, ha, fun m hm => ?_, fun v => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
          simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm', ei m' hm', hb,
            isMember]
        · rw [G_enc p mp]
          exact ⟨Or.inl, fun h => h.elim id fun h => absurd h.1 meet⟩) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by
    unfold Elixir.Module.Types.Descr.«apply_disjoint/2»; simp [rdom, encP, run m hm], fun v => ?_⟩
  rw [s]
  simp only [fe.none.2, false_or, List.mem_map, semP]
  constructor
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, (G_enc p mp v).mp h⟩
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, (G_enc p mp v).mpr h⟩

theorem inDomR_exists : ∀ (ts : List (V → Prop)), (∀ t ∈ ts, ∃ v, t v) → ∃ w, FunSem.InDomR ts w
  | [], _ => ⟨[], trivial⟩
  | t :: ts, h => by
    obtain ⟨v, hv⟩ := h t List.mem_cons_self
    obtain ⟨w, hw⟩ := inDomR_exists ts fun u mu => h u (List.mem_cons_of_mem _ mu)
    exact ⟨v :: w, hv, hw⟩

/-- Arguments with no row are covered by the domains of the positive arrows. -/
theorem noRow_cover (P : List (FunSem.Arrow V)) (t : List (V → Prop)) (s : V → Prop)
    (h : FunSem.NoRow (t.map (false, ·)) (false, fun v => ¬s v) P) :
    ∀ x, FunSem.InDomR t x → ∃ p ∈ P, FunSem.InDomR p.1 x := by
  intro x hx
  apply Classical.byContradiction
  intro hn
  refine h (x.map some) none ((FunSem.inDom_args t _).mp ((FunSem.inDom_real t x).mpr hx)) rfl fun p mp hd => ?_
  exact absurd ⟨p, mp, (FunSem.inDom_real p.1 x).mp hd⟩ hn

/-- Arguments in disjoint domains, position by position. -/
def DisjDom (a b : FunSem.Arrow V) : Prop := ∀ x, FunSem.InDomR a.1 x → FunSem.InDomR b.1 x → False

theorem disjoint_args_sem (fe : FunElem E den K seen) : ∀ (l₁ l₂ : List Term), (∀ a ∈ l₁, E a) → (∀ a ∈ l₂, E a) →
    l₁.length = l₂.length → ∃ b : Bool,
      (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m) (Term.list l₁) (Term.list l₂) =
        .ok (boolAtom b)) ∧
      (b = Bool.true → ∀ x, FunSem.InDomR (l₁.map den) x → FunSem.InDomR (l₂.map den) x → False)
  | [], [], _, _, _ => ⟨Bool.false, fun m _ => by
      unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»; simp, by simp⟩
  | a :: l₁, b :: l₂, h₁, h₂, len => by
    obtain ⟨d, hd, sd⟩ := fe.disj (h₁ a List.mem_cons_self) (h₂ b List.mem_cons_self)
    obtain ⟨r, hr, sr⟩ := disjoint_args_sem fe l₁ l₂ (fun x m => h₁ x (List.mem_cons_of_mem _ m))
      (fun x m => h₂ x (List.mem_cons_of_mem _ m)) (by simpa using len)
    refine ⟨d || r, fun m hm => ?_, fun hb x hx hy => ?_⟩
    · unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»
      rw [hd m hm, hr m hm]
      cases d <;> cases r <;> simp [Lynx.Except.orElse, boolAtom]
    · cases x with
      | nil => exact hx.elim
      | cons v x =>
        obtain ⟨hv₁, hx₁⟩ := hx
        obtain ⟨hv₂, hx₂⟩ := hy
        rcases Bool.or_eq_true _ _ |>.mp hb with h | h
        · exact sd h v hv₁ hv₂
        · exact sr h x hx₁ hx₂
  | [], _ :: _, _, _, len => by simp at len
  | _ :: _, [], _, _, len => by simp at len

theorem all_disjoint_sem (fe : FunElem E den K seen) (n : Nat) : ∀ P : List (Term × List Term × Term), PosOk E n P →
    ∃ b : Bool, (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«all_disjoint_arguments?/1» (D m) (encP P) = .ok (boolAtom b)) ∧
      (b = Bool.true → List.Pairwise DisjDom (semP den P))
  | [], _ => ⟨Bool.true, fun m _ => by
      unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»; simp [encP, Term.list], fun _ => by simp [semP]⟩
  | p :: rest, hP => by
    obtain ⟨hargs, -, plen⟩ := hP p List.mem_cons_self
    have hrest : PosOk E n rest := fun q mq => hP q (List.mem_cons_of_mem _ mq)
    obtain ⟨b₂, r₂, s₂⟩ := all_disjoint_sem fe n rest hrest
    let res : Term → Bool := fun t => bp (∃ q ∈ rest, t = .tuple #[q.1, Term.list q.2.1, q.2.2] ∧
      ∃ b : Bool, b = Bool.true ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m)
        (Term.list p.2.1) (Term.list q.2.1) = .ok (boolAtom b))
    have each : ∀ q ∈ rest, ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m)
        (Term.list p.2.1) (Term.list q.2.1) = .ok (boolAtom b)) ∧ res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = b ∧
        (b = Bool.true → DisjDom (p.2.1.map den, den p.2.2) (q.2.1.map den, den q.2.2)) := by
      intro q mq
      obtain ⟨hargs', -, qlen⟩ := hrest q mq
      obtain ⟨b, hb, sb⟩ := disjoint_args_sem fe p.2.1 q.2.1 hargs hargs' (by omega)
      refine ⟨b, hb, ?_, fun h x hx hy => sb h x hx hy⟩
      cases b
      · refine bp_false.mpr fun ⟨q', mq', e, b', hb', run⟩ => ?_
        obtain ⟨-, el, -⟩ := enc_inj e
        rw [← el] at run
        have := (run K (Nat.le_refl _)).symm.trans (hb K (Nat.le_refl _))
        subst hb'
        simp [boolAtom] at this
      · exact bp_true.mpr ⟨q, mq, rfl, Bool.true, rfl, hb⟩
    let b₁ := (rest.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).all res
    refine ⟨b₁ && b₂, fun m hm => ?_, fun hb => ?_⟩
    · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      have run₁ := all_list (D (m' + 1)) "Elixir.Module.Types.Descr" "-all_disjoint_arguments?/1-fun-0-"
        #[Term.list p.2.1] res (rest.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]) (by
          intro t mt
          obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
          obtain ⟨b, hb, rb, -⟩ := each q mq
          rw [Erlang.program.«Elixir.Module.Types.Descr:-all_disjoint_arguments?/1-fun-0-/1».pure, rb]
          simp only [Elixir.Module.Types.Descr.«-all_disjoint_arguments?/1-fun-0-/2»]
          exact hb m' hm')
      unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»
      simp only [encP, List.map_cons, Term.list] at run₁ r₂ ⊢
      simp only [pure_bind, run₁, r₂ (m' + 1) hm, andAlso_bool]; rfl
    · obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hb
      simp only [semP, List.map_cons, List.pairwise_cons]
      refine ⟨fun a ma => ?_, s₂ h₂⟩
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp ma
      obtain ⟨b, -, rb, sb⟩ := each q mq
      have : res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = Bool.true :=
        List.all_eq_true.mp h₁ _ (List.mem_map.mpr ⟨q, mq, rfl⟩)
      rw [rb] at this
      exact sb this

theorem nonempty_args_sem (fe : FunElem E den K seen) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (name : String) (lam : ∀ d a, (D (d + 1)).pure (.function "Elixir.Module.Types.Descr" name 1 #[seen]) #[a] =
      (do let e ← Elixir.Module.Types.Descr.«empty_seen?/2» (D d) a seen; Erlang.erlang.«not/1» e))
    {m : Nat} (hm : K + 1 ≤ m) :
    Erlang.lists.«all/2» (D m) (.function "Elixir.Module.Types.Descr" name 1 #[seen]) (Term.list args) =
      .ok (boolAtom (bp (∀ a ∈ args, ∃ v, den a v))) := by
  obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
  have run := all_list (D (m' + 1)) "Elixir.Module.Types.Descr" name #[seen] (fun a => !isEmpty den a) args
    (fun a ma => by
      rw [lam, fe.phi.empty (hargs a ma) m' hm']
      cases isEmpty den a <;> rfl)
  rw [run]
  congr 2
  cases h : args.all (fun a => !isEmpty den a)
  · symm; refine bp_false.mpr fun hall => ?_
    obtain ⟨a, ma, ha⟩ := List.all_eq_false.mp h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at ha
    obtain ⟨v, hv⟩ := hall a ma
    exact absurd hv ((isEmpty_iff den a).mp (by simpa using ha) v)
  · symm; refine bp_true.mpr fun a ma => ?_
    have := List.all_eq_true.mp h a ma
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
    apply Classical.byContradiction
    intro hn
    have : isEmpty den a = Bool.true := (isEmpty_iff den a).mpr fun v hv => hn ⟨v, hv⟩
    simp_all

/-- `disjoint_non_empty_domains?/3` takes a shortcut only when the arguments are not empty, and the disjoint one
only when the domains of the positive arrows are disjoint. -/
theorem domains_sem (fe : FunElem E den K seen) (n : Nat) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ v, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3» (D m) (Term.list args) (encP P) seen = .ok v) ∧
      (v = .atom "nil" ∨ ((∀ a ∈ args, ∃ x, den a x) ∧
        (v = .atom "non_empty" ∨ (v = .atom "disjoint_non_empty" ∧ List.Pairwise DisjDom (semP den P))))) := by
  let a₁ := bp (∀ a ∈ args, ∃ v, den a v)
  have h₁ : ∀ m, K + 1 ≤ m → Erlang.lists.«all/2» (D m)
      (.function "Elixir.Module.Types.Descr" "-disjoint_non_empty_domains?/3-fun-0-" 1 #[seen]) (Term.list args) =
      .ok (boolAtom a₁) := fun m hm => nonempty_args_sem fe args hargs _ (fun d a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-disjoint_non_empty_domains?/3-fun-0-/1».pure]; rfl) hm
  obtain ⟨a₂, h₂⟩ := all_uni (K + 2) "Elixir.Module.Types.Descr" "-all_non_empty_arguments?/2-fun-1-" #[seen]
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (fun t mt => by
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs', -, -⟩ := hP p mp
      refine ⟨bp (∀ a ∈ p.2.1, ∃ v, den a v), fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      dsimp only
      rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-1-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-all_non_empty_arguments?/2-fun-1-/2»]
      exact nonempty_args_sem fe p.2.1 hargs' _ (fun d a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-0-/1».pure]; rfl) (by omega))
  obtain ⟨dj, hdj, sdj⟩ := all_disjoint_sem fe n P hP
  refine ⟨if a₁ && a₂ then (if dj then .atom "disjoint_non_empty" else .atom "non_empty") else .atom "nil",
    fun m hm => ?_, ?_⟩
  · have e₁ := h₁ m (by omega)
    have e₂ := h₂ m hm
    have e₃ := hdj m (by omega)
    dsimp only at e₂
    unfold Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3»
    simp only [Elixir.Module.Types.Descr.«all_non_empty_arguments?/2», pure_bind, e₁, encP, e₂, andAlso_bool]
    simp only [encP] at e₃
    cases a₁ <;> cases a₂ <;> cases dj <;>
      simp [e₃, Lynx.Except.andAlso, Erlang.erlang.«/=/2», boolAtom]
  · by_cases ha : (a₁ && a₂) = Bool.true
    · have ne : ∀ a ∈ args, ∃ x, den a x := bp_true.mp (Bool.and_eq_true _ _ |>.mp ha).1
      rw [ite_eq_left ha]
      cases dj
      · exact Or.inr ⟨ne, Or.inl rfl⟩
      · exact Or.inr ⟨ne, Or.inr ⟨rfl, sdj rfl⟩⟩
    · have ha' : (a₁ && a₂) = Bool.false := by simpa using ha
      simp [ha']

/-- `phi_starter/4` decides whether the positive arrows are in the arrow from `args` to `ret`, when the domains of
the positive arrows cover the arguments: by `phi/5`, or by its shortcuts. -/
theorem phi_starter_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (len : args.length = n) {ret : Term} (hret : E ret) (P : List (Term × List Term × Term))
    (hP : PosOk E n P) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«phi_starter/4» (D m) (Term.list args) ret (encP P) seen = .ok (boolAtom b)) ∧
      ((∀ x, FunSem.InDomR (args.map den) x → ∃ p ∈ semP den P, FunSem.InDomR p.1 x) →
        (b = Bool.true ↔ FunSem.NoRow ((args.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den ret v) (semP den P))) := by
  obtain ⟨v, rv, hv⟩ := domains_sem fe n args hargs P hP
  have lP : ∀ p ∈ semP den P, p.1.length = ((args.map den).map (Bool.false, ·)).length := by
    intro p mp
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
    simp [(hP q mq).2.2, len]
  rcases hv with rfl | ⟨ne, rfl | ⟨rfl, disj⟩⟩
  · obtain ⟨neg, hneg, rneg, sneg⟩ := fe.neg hret
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" 1 #[])
        (Term.list args) = .ok (encA (args.map fun x => (Bool.false, x))) := fun m => by
      have := map_list (D m) "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" #[]
        (fun x => .tuple #[boolAtom Bool.false, x]) args fun x _ => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-phi_starter/4-fun-0-/1».pure]; rfl
      rw [this]; simp only [encA, List.map_map]; rfl
    obtain ⟨b, c, run, sb, -⟩ := phi_run fe.phi (m := K + 2) (by omega) P hP (args.map fun x => (Bool.false, x))
      (Bool.false, neg) (.map []) (by simpa using hargs) (by simpa using len) hneg (cacheOk_nil E den n)
    have dneg : den neg = fun v => ¬den ret v := funext fun v => propext (sneg v)
    have sem : FunSem.phiS (semA den (args.map fun x => (Bool.false, x))) (semR den (Bool.false, neg)) (semP den P) ↔
        FunSem.NoRow ((args.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den ret v) (semP den P) := by
      have e : semA den (args.map fun x => (Bool.false, x)) = (args.map den).map (Bool.false, ·) := by simp [semA]
      rw [e, semR, dneg]
      exact FunSem.phiS_iff _ _ _ lP
    refine ⟨b, fun m hm => ?_, fun _ => sb.trans sem⟩
    obtain ⟨b', c', run', sb', -⟩ := phi_run fe.phi (m := m) (by omega) P hP (args.map fun x => (Bool.false, x))
      (Bool.false, neg) (.map []) (by simpa using hargs) (by simpa using len) hneg (cacheOk_nil E den n)
    have bb : b' = b := by
      cases b <;> cases b' <;> simp_all
    subst bb
    unfold Elixir.Module.Types.Descr.«phi_starter/4»
    simp only [encR, boolAtom_false] at run'
    simp [rv m hm, margs, rneg m (by omega), run']
  · obtain ⟨w, hw⟩ := inDomR_exists (args.map den) fun t mt => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt; exact ne a ma
    obtain ⟨r, hr, ra, sr⟩ := apply_static_sem fe fd n args hargs P hP
    refine ⟨bp (∀ v, den r v → den ret v), fun m hm => ?_, fun cover => ?_⟩
    · unfold Elixir.Module.Types.Descr.«phi_starter/4»
      simp [rv m hm, ra m (by omega), fe.sub hr hret m (by omega)]
    · rw [bp_true, FunSem.noRow_app _ _ _ w hw cover]
      exact forall_congr' fun v => imp_congr_left (sr v)
  · obtain ⟨w, hw⟩ := inDomR_exists (args.map den) fun t mt => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt; exact ne a ma
    obtain ⟨r, hr, ra, sr⟩ := apply_disjoint_sem fe fd n args hargs P hP
    refine ⟨bp (∀ v, den r v → den ret v), fun m hm => ?_, fun cover => ?_⟩
    · unfold Elixir.Module.Types.Descr.«phi_starter/4»
      simp [rv m hm, ra m (by omega), fe.sub hr hret m (by omega)]
    · have dj : ∀ i j (hi : i < (semP den P).length) (hj : j < (semP den P).length), i ≠ j →
          ∀ x, FunSem.InDomR (semP den P)[i].1 x → ¬FunSem.InDomR (semP den P)[j].1 x := by
        intro i j hi hj ne x h₁ h₂
        have pw := List.pairwise_iff_getElem.mp disj
        rcases Nat.lt_or_gt_of_ne ne with lt | lt
        · exact pw i j hi hj lt x h₁ h₂
        · exact pw j i hj hi lt x h₂ h₁
      rw [bp_true, FunSem.noRow_app _ _ _ w hw cover,
        FunSem.app_disjoint _ _ ⟨w, hw⟩ dj cover]
      constructor
      · intro h p mp hx v hv
        exact h v ((sr v).mpr ⟨p, mp, hx, hv⟩)
      · intro h v hv
        obtain ⟨p, mp, hx, hp⟩ := (sr v).mp hv
        exact h p mp hx v hp

/-- The negative arrows a line of positive arrows `P` is contained in, as `phi` sees them. -/
def NegIn (_n : Nat) (den : Term → V → Prop) (P : List (Term × List Term × Term)) (q : Term × List Term × Term) : Prop :=
  FunSem.NoRow ((q.2.1.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den q.2.2 v) (semP den P)

/-- Lines with positive arrows: the line is empty exactly when some negative arrow contains the positive ones. -/
theorem fun_line_pos_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat)
    (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N) (ne : P ≠ []) :
    ∃ b : Bool, (∀ m, K + 3 ≤ m →
      Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N) seen = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∃ q ∈ N, NegIn n den P q) := by
  obtain ⟨fdom, hfdom, rfdom, sfdom⟩ := fetch_domain_sem fd n P hP
  let res : Term → Bool := fun t => bp (∃ q ∈ N, t = .tuple #[q.1, Term.list q.2.1, q.2.2] ∧ NegIn n den P q)
  have each : ∀ q ∈ N, res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = bp (NegIn n den P q) ∧ ∀ m, K + 2 ≤ m →
      (Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3» (D m) (encP P) seen
        (.tuple #[q.1, Term.list q.2.1, q.2.2])) = .ok (boolAtom (bp (NegIn n den P q))) := by
    intro q mq
    refine ⟨bp_congr ⟨fun ⟨q', mq', e, h⟩ => ?_, fun h => ⟨q, mq, rfl, h⟩⟩, fun m hm => ?_⟩
    · obtain ⟨-, el, er⟩ := enc_inj e
      simp only [NegIn] at h ⊢
      rw [el, er]; exact h
    obtain ⟨hargs, hret, len⟩ := hN q mq
    obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom q.2.1 hargs
    obtain ⟨c, hc, rc, sc⟩ := fd.diff hdom hfdom
    obtain ⟨b, rb, sb⟩ := phi_starter_sem fe fd n q.2.1 hargs len hret P hP
    have cover : bp (∀ x, ¬dden c x) = Bool.true ↔
        ∀ x, FunSem.InDomR (q.2.1.map den) x → ∃ p ∈ semP den P, FunSem.InDomR p.1 x := by
      rw [bp_true]
      refine forall_congr' fun x => ?_
      rw [sc, sdom, sfdom]
      constructor
      · intro h hx; apply Classical.byContradiction; exact fun hn => h ⟨hx, hn⟩
      · exact fun h ⟨hx, hn⟩ => hn (h hx)
    simp only [Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3», rdom, rfdom m (by omega),
      Elixir.Module.Types.Descr.«subtype_seen?/3», rc m (by omega), fd.emptySeen hc m (by omega), rb m hm,
      Lynx.Except.ok_bind, andAlso_bool]
    congr 2
    cases hcv : bp (∀ x, ¬dden c x)
    · symm; refine bp_false.mpr fun h => ?_
      have := cover.mpr (noRow_cover _ _ _ h)
      rw [hcv] at this; cases this
    · have cv := cover.mp hcv
      cases hb : b
      · symm; exact bp_false.mpr fun h => by have := (sb cv).mpr h; rw [hb] at this; cases this
      · symm; exact bp_true.mpr ((sb cv).mp hb)
  have run : ∀ m, K + 3 ≤ m → Erlang.lists.«any/2» (D m)
      (.function "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-1-" 1 #[encP P, seen])
      (Term.list (N.map fun q => .tuple #[q.1, Term.list q.2.1, q.2.2])) =
      .ok (boolAtom ((N.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).any res)) := fun m hm => by
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    refine any_list _ _ _ _ res _ fun t mt => ?_
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-1-/1».pure, (each q mq).2 m' hm',
      (each q mq).1]
  refine ⟨(N.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).any res, fun m hm => ?_, ?_⟩
  · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil ne
    rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
    have r := run m hm
    simp only [encP, List.map_cons, Term.list] at r ⊢
    simp only [pure_bind]
    exact r
  · rw [List.any_eq_true]
    constructor
    · rintro ⟨t, mt, ht⟩
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
      rw [(each q mq).1, bp_true] at ht
      exact ⟨q, mq, ht⟩
    · rintro ⟨q, mq, h⟩
      exact ⟨_, List.mem_map.mpr ⟨q, mq, rfl⟩, by rw [(each q mq).1, bp_true]; exact h⟩

theorem lineEmpty_negIn (n : Nat) (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N)
    (ne : P ≠ []) : FunSem.LineEmpty n (semP den P) (semP den N) ↔ ∃ q ∈ N, NegIn n den P q := by
  have lP : ∀ p ∈ semP den P, p.1.length = n := by
    intro p mp
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
    simp [(hP q mq).2.2]
  rw [FunSem.lineEmpty_iff]
  constructor
  · rintro ⟨q', mq', h⟩
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mq'
    have lt : (q.2.1.map den).length = n := by simp [(hN q mq).2.2]
    refine ⟨q, mq, ?_⟩
    have := (FunSem.neg_iff_phi n _ (by simpa [semP] using ne) lP _ _ lt).mp h
    exact (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [(hN q mq).2.2])).mp this
  · rintro ⟨q, mq, h⟩
    have lt : (q.2.1.map den).length = n := by simp [(hN q mq).2.2]
    refine ⟨_, List.mem_map.mpr ⟨q, mq, rfl⟩, ?_⟩
    refine (FunSem.neg_iff_phi n _ (by simpa [semP] using ne) lP _ _ lt).mpr ?_
    exact (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [(hN q mq).2.2])).mpr h

/-- `fun_line_empty?/3` decides whether a line of arrows of arity `n` is empty, from call depth `K + 3`. -/
theorem fun_line_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat)
    (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N) :
    ∃ b : Bool, (∀ m, K + 3 ≤ m →
      Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N) seen = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ FunSem.LineEmpty n (semP den P) (semP den N)) := by
  by_cases ne : P ≠ []
  · obtain ⟨b, rb, sb⟩ := fun_line_pos_sem fe fd n P N hP hN ne
    exact ⟨b, rb, sb.trans (lineEmpty_negIn n P N hP hN ne).symm⟩
  simp only [ne_eq, Decidable.not_not] at ne
  subst ne
  cases N with
  | nil =>
    refine ⟨Bool.false, fun m _ => ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]; simp [encP, Term.list]
    · simp only [semP, List.map_nil]
      exact ⟨fun h => (by cases h), fun h => absurd h (FunSem.lineEmpty_nil n)⟩
  | cons q qs =>
    obtain ⟨hargs, -, len⟩ := hN q List.mem_cons_self
    obtain ⟨kt, leaf⟩ := leaf_fun (q.2.1.map fun _ => .map [])
    let top : Term × List Term × Term := (.integer kt, q.2.1.map fun _ => .map [], .atom "term")
    have hT : PosOk E n [top] := fun t mt => by
      rw [List.mem_singleton.mp mt]
      exact ⟨fun a ma => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ma; exact fe.none.1, fe.term.1, by simp [top, len]⟩
    obtain ⟨b, rb, sb⟩ := fun_line_pos_sem fe fd n [top] (q :: qs) hT hN (by simp)
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-0-" 1 #[])
        (Term.list q.2.1) = .ok (Term.list (q.2.1.map fun _ => .map [])) := fun m =>
      map_list (D m) _ _ _ _ _ fun x _ => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-0-/1».pure]; rfl
    have semT : semP den [top] = [FunSem.top n] := by
      simp only [semP, List.map_cons, List.map_nil, List.map_map, FunSem.top, top]
      have e₁ : (den ∘ fun _ : Term => Term.map []) = fun _ => fun _ => False :=
        funext fun _ => funext fun v => propext (iff_false_intro (fe.none.2 v))
      have e₂ : den (.atom "term") = fun _ => True := funext fun v => propext (iff_true_intro (fe.term.2 v))
      rw [e₁, e₂, List.map_const', len]
    refine ⟨b, fun m hm => ?_, ?_⟩
    · have r := rb m hm
      rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
      simp only [encP, List.map_cons, List.map_nil, Term.list, top] at r ⊢
      simp [margs, leaf]
      exact r
    · rw [sb, ← lineEmpty_negIn n [top] (q :: qs) hT hN (by simp), semT]
      simp only [semP, List.map_nil]
      exact (FunSem.lineEmpty_top n _).symm

end

end Elixir.STTDescrProofsTest.Nest
