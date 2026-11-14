namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of tuple types of element types on tuples of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Public emptiness checks of element types are exact. -/
theorem EF.empty_pub (ef : EF nd E V den tl K) {a : Term} (ha : E a) :
    ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∀ v, ¬den a v) := by
  obtain ⟨b, run, ex⟩ := ef.empty [] ha
  have exact := ex (lh a + 1) (by omega) (safeN_nil _)
  rcases ef.static ha with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩
  · refine ⟨Bool.false, fun m _ => rfl, ?_⟩
    obtain ⟨v⟩ := ef.inhabited
    exact ⟨fun h => absurd h (by decide), fun h => absurd (ef.den_term v) (h v)⟩
  · exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm, exact⟩
  · exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm, exact⟩

theorem opt_tuple_funG (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) {a b : Term} (ha : E a) (hb : E b)
    (S : List (Term × Term)) :
    ∃ c, E c ∧ (∀ v, den c v ↔ den a v ∧ den b v) ∧
      Lynx.Dispatcher.pure (D (n + 2)) (optTupleIFun (.map S)) #[a, b] = .ok c := by
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S ha hb hn
  refine ⟨c, hc, sem, ?_⟩
  rw [optTupleIFun, Erlang.program.«Elixir.Module.Types.Descr:-opt_tuple_leaf_intersection/3-fun-0-/2».pure]
  simpa [Elixir.Module.Types.Descr.«-opt_tuple_leaf_intersection/3-fun-0-/3»] using run

/-- Element intersections that are never empty, or the `:empty` throw when one of them is. -/
theorem zip_ne_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) (S : List (Term × Term)) :
    ∀ (l₁ : List Term), (∀ e ∈ l₁, E e) → ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc : List Term,
      (∃ r : List Term, Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list l₁)
          (Term.list l₂) (Term.list acc) (optTupleIFun (Term.map S)) = .ok (Term.list (acc.reverse ++ r)) ∧
        (∀ e ∈ r, E e) ∧ r.length = max l₁.length l₂.length ∧
        ∀ v, InT den Bool.false r v ↔ InT den Bool.false l₁ v ∧ InT den Bool.false l₂ v) ∨
      (Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list l₁)
          (Term.list l₂) (Term.list acc) (optTupleIFun (.map S)) = .error (.throw (.atom "empty")) ∧
        ∀ v, InT den Bool.false l₁ v → InT den Bool.false l₂ v → False) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro _ l₂ h₂ acc
    refine Or.inl ⟨l₂, ?_, h₂, by simp, fun v => by simp [InT.open_nil]⟩
    unfold Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4»
    exact reverse_list acc l₂
  | cons x xs ih =>
    intro h₁ l₂ h₂ acc
    cases l₂ with
    | nil =>
      refine Or.inl ⟨x :: xs, ?_, h₁, by simp, fun v => by simp [InT.open_nil]⟩
      unfold Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4»
      exact reverse_list acc (x :: xs)
    | cons y ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      obtain ⟨e, he, sem, run⟩ := opt_tuple_funG ef hn hx hy S
      obtain ⟨b, runb', iffb⟩ := ef.empty_pub he
      have runb := runb' (n + 2) (by omega)
      have step : Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list (x :: xs))
          (Term.list (y :: ys)) (Term.list acc) (optTupleIFun (.map S)) =
          if b then .error (.throw (.atom "empty"))
          else Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list xs) (Term.list ys)
            (Term.list (e :: acc)) (optTupleIFun (.map S)) := by
        rw [Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4».eq_def]
        cases b <;> simp [Term.list, Elixir.Module.Types.Descr.«non_empty_intersection!/3», run, runb, boolAtom,
          isMember]
      cases b
      · rw [step]; simp only [Bool.false_eq_true, ite_false]
        rcases ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys (fun e me => h₂ e (List.mem_cons_of_mem _ me))
          (e :: acc) with ⟨r, runr, hr, len, semr⟩ | ⟨runr, empty⟩
        · refine Or.inl ⟨e :: r, by simpa using runr, fun e' me => ?_, by simp [len], fun v => ?_⟩
          · rcases List.mem_cons.mp me with rfl | me
            · exact he
            · exact hr e' me
          · cases v with
            | nil => simp [InT]
            | cons z v =>
              simp only [InT, semr v, sem z]
              exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
        · refine Or.inr ⟨runr, fun v i₁ i₂ => ?_⟩
          cases v with
          | nil => exact i₁
          | cons z v => exact empty v i₁.2 i₂.2
      · rw [step]
        refine Or.inr ⟨by simp, fun v i₁ i₂ => ?_⟩
        cases v with
        | nil => exact i₁
        | cons z v => exact (iffb.mp rfl) z ((sem z).mpr ⟨i₁.1, i₂.1⟩)

/-- Literal intersections of tuples of values: `:empty` when no tuple is in both, otherwise the tuples of both. -/
theorem tuple_lit_inter_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {l₁ l₂ : List Term} (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e)
    (S : List (Term × Term)) :
    (Elixir.Module.Types.Descr.«tuple_literal_intersection/5» (D (n + 2)) (.atom t₁) (Term.list l₁) (.atom t₂)
        (Term.list l₂) (optTupleIFun (.map S)) = .ok (.atom "empty") ∧
      ∀ v, InT den (t₁ == "closed") l₁ v → InT den (t₂ == "closed") l₂ v → False) ∨
    ∃ (t : String) (l : List Term), Elixir.Module.Types.Descr.«tuple_literal_intersection/5» (D (n + 2)) (.atom t₁)
        (Term.list l₁) (.atom t₂) (Term.list l₂) (optTupleIFun (.map S)) = .ok (.tuple #[.atom t, Term.list l]) ∧
      (t = "open" ↔ t₁ = "open" ∧ t₂ = "open") ∧ (t = "open" ∨ t = "closed") ∧ (∀ e ∈ l, E e) ∧
      l.length = max l₁.length l₂.length ∧ ¬Disj t₁ t₂ l₁.length l₂.length ∧
      ∀ v, InT den (t == "closed") l v ↔ InT den (t₁ == "closed") l₁ v ∧ InT den (t₂ == "closed") l₂ v := by
  obtain ⟨sv, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  unfold Elixir.Module.Types.Descr.«tuple_literal_intersection/5»
  simp only [length_list, Lynx.Except.ok_bind, hv]
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · left
    refine ⟨by rw [disj.mpr d]; rfl, fun w hw hlw => ?_⟩
    rw [InT.iff_open] at hw hlw
    rcases d with ⟨rfl, rfl, ne⟩ | ⟨rfl, rfl, lt⟩ | ⟨rfl, rfl, lt⟩
    · exact ne (by rw [← hw.2 rfl, hlw.2 rfl])
    · have := hlw.1.length_le; have := hw.2 rfl; omega
    · have := hw.1.length_le; have := hlw.2 rfl; omega
  have nv : sv ≠ .atom "disjoint" := fun e => d (disj.mp e)
  rcases zip_ne_sem ef hn S l₁ h₁ l₂ h₂ [] with ⟨r, zip, hr, len, semr⟩ | ⟨zip, empty⟩
  · right
    simp only [List.reverse_nil, List.nil_append] at zip
    let tag : String := if t₁ = "open" ∧ t₂ = "open" then "open" else "closed"
    refine ⟨tag, r, ?_, by simp only [tag]; split <;> simp_all, by simp only [tag]; split <;> simp, hr, len, d,
      fun w => ?_⟩
    · split
      · exact absurd rfl nv
      · simp only [Term.list] at zip
        by_cases o₁ : t₁ = "open" <;> by_cases o₂ : t₂ = "open" <;>
          simp [tag, o₁, o₂, Erlang.erlang.«==/2», Lynx.Except.andAlso, zip]
    rw [InT.iff_open, InT.iff_open (l := l₁), InT.iff_open (l := l₂), semr w]
    have nd : ¬Disj t₁ t₂ l₁.length l₂.length := d
    simp only [Disj, not_or, not_and] at nd
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> simp [tag, len] at nd ⊢
    all_goals first
      | (rw [Nat.max_eq_right nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩)
      | (rw [Nat.max_eq_left nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩)
      | (rw [nd, Nat.max_self]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b, c⟩, fun ⟨⟨a, c⟩, b, _⟩ => ⟨⟨a, b⟩, c⟩⟩)
  · left
    refine ⟨?_, fun w hw hlw => empty w (InT.iff_open.mp hw).1 (InT.iff_open.mp hlw).1⟩
    split
    · exact absurd rfl nv
    · simp [Term.list] at zip
      simp [zip, Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason]

/-- `tuple_closed_subtype_of_open?/2` only answers true when every tuple of the closed literal is in the open one. -/
theorem tcso_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (cl l : List Term), (∀ e ∈ cl, E e) → (∀ e ∈ l, E e) →
    ∃ c : Bool, Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2» (D m) (Term.list cl) (Term.list l) =
        .ok (boolAtom c) ∧ (c = Bool.true → ∀ v, InT den Bool.true cl v → InT den Bool.false l v) := by
  intro cl
  induction cl with
  | nil =>
    intro l _ _
    cases l with
    | nil =>
      refine ⟨Bool.true, ?_, fun _ v _ => InT.open_nil v⟩
      rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def]; simp [boolAtom]
    | cons y ys =>
      refine ⟨Bool.false, ?_, fun h => by cases h⟩
      rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def]; simp [boolAtom]
  | cons x xs ih =>
    intro l h₁ h₂
    cases l with
    | nil =>
      refine ⟨Bool.true, ?_, fun _ v _ => InT.open_nil v⟩
      rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def]; simp [boolAtom]
    | cons y ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      obtain ⟨bs, hbs', sound'⟩ := ef.sub hx hy
      have hbs : Elixir.Module.Types.Descr.«subtype?/2» (D m) x y = .ok (boolAtom bs) := hbs' m hm
      obtain ⟨c, run, sound⟩ := ih ys (fun e me => h₁ e (List.mem_cons_of_mem _ me))
        (fun e me => h₂ e (List.mem_cons_of_mem _ me))
      refine ⟨bs && c, ?_, fun h v hv => ?_⟩
      · rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def, list_cons, list_cons]
        simp only
        rw [hbs, run, andAlso_bool]
      · simp only [Bool.and_eq_true] at h
        cases v with
        | nil => exact hv.elim
        | cons z v =>
          refine ⟨sound' h.1 z hv.1, sound h.2 v hv.2⟩

/-! Clauses of `opt_tuple_intersection/3`. -/

theorem opt_tuple_inter_top_eq {d : Dispatcher} {x S : Term} {k : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x (.tuple #[k, .atom "open", .nil]) S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  · exact (hx _ rfl).elim
  · rfl
  all_goals rename_i h
  all_goals first | exact (h _ rfl).elim | (exfalso; simp_all)

theorem opt_tuple_inter_plain_eq {d : Dispatcher} {x y S : Term} (tx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ty : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (h3 : ∀ a b c a' b' c', x = .tuple #[a, b, c] → y = .tuple #[a', b', c'] → False)
    (h4 : ∀ k fo a b c u e, x = .tuple #[k, .atom "open", fo] → y = .tuple #[a, b, c, u, e] → False)
    (h5 : ∀ k fo a b c u e, y = .tuple #[k, .atom "open", fo] → x = .tuple #[a, b, c, u, e] → False) :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = Elixir.Module.Types.Descr.«tuple_intersection/2» x y := by
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := by
    rintro a b c rfl e
    obtain ⟨_, _, _, rfl, -⟩ := exact_tuple3 e
    exact h3 _ _ _ _ _ _ rfl rfl
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  · exact (tx _ rfl).elim
  · exact (ty _ rfl).elim
  · simp only [leaf_guard]
    split
    · rw [ite_eq_right (ne _ _ _ rfl)]
      split
      all_goals first
        | rfl
        | exact (h3 _ _ _ _ _ _ rfl rfl).elim
        | (exfalso; simp_all
           first
             | exact h4 _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
             | exact h5 _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl)
    · split
      all_goals first
        | rfl
        | exact (h3 _ _ _ _ _ _ rfl rfl).elim
        | exact (h4 _ _ _ _ _ _ _ rfl rfl).elim
        | exact (h5 _ _ _ _ _ _ _ rfl rfl).elim

/-- Exactly equal tuple leaves intersect to the first. -/
theorem opt_tuple_inter_same {d : Dispatcher} {S k a b y : Term} (nt : ¬IsTop (.tuple #[k, a, b]))
    (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d (.tuple #[k, a, b]) y S = .ok (.tuple #[k, a, b]) := by
  obtain ⟨a', b', c', rfl, e₁, e₂, e₃⟩ := exact_tuple3 e
  have ny : ∀ k', Term.tuple #[a', b', c'] ≠ .tuple #[k', .atom "open", .nil] := by
    intro k' h
    obtain ⟨-, rfl, rfl⟩ := tuple3_inj h
    have f₂ := Lynx.Term.compareExact_eq_symm e₂
    have f₃ := Lynx.Term.compareExact_eq_symm e₃
    simp only [compareExact_eq_atom, compareExact_eq_nil] at f₂ f₃
    subst f₂ f₃
    exact nt ⟨_, rfl⟩
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  · rename_i heq; exact absurd ⟨_, heq⟩ nt
  · rename_i h₁ h₂; first | exact (ny _ h₂).elim | exact (ny _ h₁).elim
  · simp only [leaf_guard]
    rw [ite_eq_left (by simpa using e)]
    rfl

theorem opt_tuple_inter_leaves {d : Dispatcher} {S : Term} {x y : Term} (hx : TupleOk E x)
    (hy : TupleOk E y) (ne : compareExact (fuel y x) y x ≠ .eq) :
    (Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "tuple_intersection") x y = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = Elixir.Module.Types.Descr.«tuple_intersection/2» x y) ∧
    (∀ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "tuple_intersection") x y = .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S =
        Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3» d x y S') := by
  obtain ⟨⟨k₁, t₁, l₁, rfl, -, -⟩, nt₁⟩ := hx
  obtain ⟨⟨k₂, t₂, l₂, rfl, -, -⟩, nt₂⟩ := hy
  constructor <;> intros <;>
  · unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
    split
    · rename_i heq; exact absurd ⟨_, heq⟩ nt₁
    · rename_i h₁ h₂; first | exact absurd ⟨_, h₁⟩ nt₂ | exact absurd ⟨_, h₂⟩ nt₂
    simp only [leaf_guard]
    rw [ite_eq_right (by simpa using ne)]
    simp_all

theorem opt_tuple_inter_push_l {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d (.tuple #[k, .atom "open", fo]) (.tuple #[h, lit, c, u, e]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function "Elixir.Module.Types.Descr" "tuple_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

theorem opt_tuple_inter_push_r {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function "Elixir.Module.Types.Descr" "tuple_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

theorem tlit_closed_neg {k : Int} {cl : Term} (h : TLit E (.tuple #[.integer k, .atom "closed", cl])) : k < 0 := by
  obtain ⟨⟨⟨k', t, l, e, -, -⟩, -⟩, key⟩ := h
  obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
  simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
  subst e₁ e₂ e₃
  exact (key _ _ _ rfl).1 rfl

/-- Pushing an open literal below closed literals of negative keys keeps exactly the tuples of both. -/
theorem push_open (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {H : Int} (hH : 0 ≤ H) {l : List Term}
    (hL : TLit E (.tuple #[.integer H, .atom "open", Term.list l])) {b : Term} (wb : Bdd (TLit E) b) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» (D m) b (.tuple #[.integer H, .atom "open", Term.list l])
        (.function "Elixir.Module.Types.Descr" "tuple_closed_subtype_of_open?" 2 #[]) = .ok r ∧
      TField E r ∧ ∀ v, denTF E den r v = (denTF E den b v && denTF E den (.tuple #[.integer H, .atom "open", Term.list l]) v) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  have hl₀ : ∀ e ∈ l, E e := tupleLit_elems hL.1.1
  obtain ⟨r, run, okr, semr⟩ := open_leaf_ok (Val := fun ρ => ∃ v, ρ = valT E den v) (fun ρ ⟨v, e⟩ => e ▸ valT_resp v)
    (ok := TLit E) (d := D (n + 1)) hL
    (fun k cl h => closed_lt_open' (tlit_closed_neg h) hH cl _)
    (fun k cl h => by
      have h₀ := h
      obtain ⟨⟨⟨k', tag, cls, e, -, -⟩, -⟩, -⟩ := h
      obtain ⟨-, -, e₂⟩ := tuple3_inj e
      subst e₂
      have hcl := tupleLit_elems h₀.1.1
      obtain ⟨c, hc, sound⟩ := tcso_val ef hn cls l hcl hl₀
      refine ⟨c, by
        rw [Erlang.program.«Elixir.Module.Types.Descr:tuple_closed_subtype_of_open?/2».pure]
        exact hc, fun ct ρ ⟨v, hv⟩ hρ => ?_⟩
      subst hv
      exact (vT_lit ef (Or.inl rfl) hl₀).mpr (sound ct v ((vT_lit ef (Or.inr rfl) hcl).mp hρ)))
    (TLit E) b wb (fun _ h => h)
  have wr : Bdd (TLit E) r := okr (TLit E) (fun _ h => h) hL
  refine ⟨r, run, Or.inr wr, fun v => ?_⟩
  rw [denTF_bdd wr, semr _ ⟨v, rfl⟩, denTF_bdd wb, denTF_bdd (Bdd.leaf_iff.mpr hL), eval_leaf]

/-- Optimized intersections of tuple literals hold the tuples of both. -/
theorem opt_tuple_leaf_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) {x y : Term} (hx : TLit E x)
    (hy : TLit E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3» (D (n + 2)) x y (.map S) = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := by
  have hx₀ := hx
  have hy₀ := hy
  obtain ⟨⟨⟨k₁, t₁, l₁, rfl, g₁, h₁⟩, nt₁⟩, key₁⟩ := hx
  obtain ⟨⟨⟨k₂, t₂, l₂, rfl, g₂, h₂⟩, nt₂⟩, key₂⟩ := hy
  have wx : Bdd (TLit E) (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) := Bdd.leaf_iff.mpr hx₀
  have wy : Bdd (TLit E) (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) := Bdd.leaf_iff.mpr hy₀
  have dx : ∀ v, denTF E den (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) v = Bool.true ↔
      InT den (t₁ == "closed") l₁ v :=
    fun v => by rw [denTF_bdd wx, eval_leaf]; exact vT_lit ef g₁ h₁
  have dy : ∀ v, denTF E den (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) v = Bool.true ↔
      InT den (t₂ == "closed") l₂ v :=
    fun v => by rw [denTF_bdd wy, eval_leaf]; exact vT_lit ef g₂ h₂
  rcases tuple_lit_inter_val ef hn g₁ g₂ h₁ h₂ S with ⟨run, empty⟩ | ⟨t, l, run, iff, g, hl, len, nd, sem⟩
  · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
    · unfold Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3»
      simp only [optTupleIFun] at run
      simp [run]
    · rw [denTF_bdd Bdd.bot]
      cases e : denTF E den (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) v
      · rfl
      · cases e' : denTF E den (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) v
        · rfl
        · exact (empty v ((dx v).mp e) ((dy v).mp e')).elim
  · obtain ⟨k, leaf, key⟩ := leaf_new_key t g l
    have okr : TLit E (.tuple #[.integer k, .atom t, Term.list l]) := by
      refine ⟨⟨⟨k, t, l, rfl, g, hl⟩, fun ⟨k', e⟩ => ?_⟩, key⟩
      obtain ⟨-, e₁, e₂⟩ := tuple3_inj e
      simp only [Term.atom.injEq] at e₁
      subst e₁
      obtain ⟨rfl, rfl⟩ := iff.mp rfl
      cases l with
      | cons _ _ => simp [Term.list] at e₂
      | nil =>
        cases l₁ with
        | cons a as => have := Nat.le_max_left (as.length + 1) l₂.length; simp at len; omega
        | nil => exact nt₁ ⟨_, rfl⟩
    have wr : Bdd (TLit E) (.tuple #[.integer k, .atom t, Term.list l]) := Bdd.leaf_iff.mpr okr
    refine ⟨_, ?_, Or.inr wr, fun v => ?_⟩
    · unfold Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3»
      simp only [optTupleIFun] at run
      simp [run, leaf]
    · apply Bool.eq_iff_iff.mpr
      rw [denTF_bdd wr, eval_leaf, vT_lit ef g hl, sem v, Bool.and_eq_true, dx, dy]

theorem tlit_leaf {k : Int} {a b : Term} (h : TLit E (.tuple #[.integer k, a, b])) :
    ∃ (t : String) (l : List Term), a = .atom t ∧ b = Term.list l ∧ (t = "open" ∨ t = "closed") ∧
      (∀ e ∈ l, E e) ∧ (t = "open" → 0 ≤ k ∧ l ≠ []) := by
  obtain ⟨⟨⟨k', t, l, e, g, hl⟩, nt⟩, key⟩ := h
  obtain ⟨e₀, e₁, e₂⟩ := tuple3_inj e
  simp only [Term.integer.injEq] at e₀
  subst e₀ e₁ e₂
  have ne : t = "open" → l ≠ [] := fun o ne => nt ⟨_, by rw [o, ne]⟩
  exact ⟨t, l, rfl, rfl, g, hl, fun o => ⟨(key _ _ _ rfl).2 o (ne o), ne o⟩⟩

/-- Optimized intersections of tuple types hold the tuples of both. -/
theorem opt_tuple_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {x y : Term} (fx : TField E x)
    (fy : TField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»; rfl, fy,
      fun v => by rw [denTF_top]; rfl⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, opt_tuple_inter_top_eq (not_top_of_ok wx tlit_not), Or.inr wx,
      fun v => by rw [denTF_top]; simp⟩
  have nx := not_top_of_ok wx tlit_not
  have ny := not_top_of_ok wy tlit_not
  have plain : Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) =
      Elixir.Module.Types.Descr.«tuple_intersection/2» x y →
      ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := by
    intro e
    obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [e, tuple_intersection_bdd nx ny, hr], Or.inr wr, fun v => ?_⟩
    rw [denTF_bdd wr, denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]
  have plainEq := fun h3 h4 h5 => plain (opt_tuple_inter_plain_eq (d := D m) (S := .map S) nx ny h3 h4 h5)
  have xAtom : ∀ {s : String}, x = .atom s → ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) =
      .ok r ∧ TField E r ∧ ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ e _ => by cases e) (fun _ _ _ _ _ _ _ e _ => by cases e)
      (fun _ _ _ _ _ _ _ _ e => by cases e)
  have yAtom : ∀ {s : String}, y = .atom s →
      ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) =
      .ok r ∧ TField E r ∧ ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ _ e => by cases e) (fun _ _ _ _ _ _ _ _ e => by cases e)
      (fun _ _ _ _ _ _ _ e _ => by cases e)
  rcases wx.shape with ex | ex | ⟨k₁, a₁, b₁, rfl⟩ | ⟨h₁, lit₁, c₁, u₁, d₁, rfl⟩
  · exact xAtom ex
  · exact xAtom ex
  all_goals rcases wy.shape with ey | ey | ⟨k₂, a₂, b₂, rfl⟩ | ⟨h₂, lit₂, c₂, u₂, d₂, rfl⟩
  all_goals try exact yAtom ey
  -- two leaves
  · have ox := (Bdd.leaf_iff).mp wx
    have oy := (Bdd.leaf_iff).mp wy
    by_cases same : compareExact (fuel (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁])) (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁]) = .eq
    · exact ⟨_, opt_tuple_inter_same ox.1.2 same, Or.inr wx,
        fun v => by rw [denTF_exact (Or.inr wx) (Or.inr wy) same, Bool.and_self]⟩
    rcases opt_bdd_seen_map S (.atom "tuple_intersection") (.tuple #[.integer k₁, a₁, b₁])
      (.tuple #[.integer k₂, a₂, b₂]) with seen | ⟨S', okS⟩
    · exact plain ((opt_tuple_inter_leaves ox.1 oy.1 same).1 seen)
    · obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      obtain ⟨n', rfl, hn'⟩ := succ_of_le hn
      obtain ⟨r, run, fr, sr⟩ := opt_tuple_leaf_val ef (n := n') (by omega) ox oy S'
      exact ⟨r, by rw [(opt_tuple_inter_leaves ox.1 oy.1 same).2 _ okS, run], fr, sr⟩
  -- a leaf and a node
  · obtain ⟨t, l, rfl, rfl, g, -, op⟩ := tlit_leaf ((Bdd.leaf_iff).mp wx)
    rcases g with rfl | rfl
    · obtain ⟨hk, ne⟩ := op rfl
      obtain ⟨r, hr, fr, sr⟩ := push_open ef (m := m) (by omega) hk ((Bdd.leaf_iff).mp wx) wy
      refine ⟨r, ?_, fr, fun v => by rw [sr v, Bool.and_comm]⟩
      rw [opt_tuple_inter_push_l (by cases l <;> simp_all [Term.list])]
      exact hr
    · exact plainEq (fun _ _ _ _ _ _ _ e => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
        (fun _ _ _ _ _ _ _ _ e => by simp at e)
  -- a node and a leaf
  · obtain ⟨t, l, rfl, rfl, g, -, op⟩ := tlit_leaf ((Bdd.leaf_iff).mp wy)
    rcases g with rfl | rfl
    · obtain ⟨hk, ne⟩ := op rfl
      obtain ⟨r, hr, fr, sr⟩ := push_open ef (m := m) (by omega) hk ((Bdd.leaf_iff).mp wy) wx
      refine ⟨r, ?_, fr, sr⟩
      rw [opt_tuple_inter_push_r (by cases l <;> simp_all [Term.list])]
      exact hr
    · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
        (fun _ _ _ _ _ _ _ e _ => by simp at e)
  -- two nodes
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun _ _ _ _ _ _ _ e _ => by simp at e)

end Elixir.STTDescrProofsTest.Nest
