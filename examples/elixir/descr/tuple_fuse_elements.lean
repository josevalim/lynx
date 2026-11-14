namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fusing tuple literals of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types with only the facts that do not involve emptiness, for lemmas that only need comparisons. -/
theorem EF.semR (ef : EF nd E V den tl K) : ElemSem E K V den (fun _ => False) where
  term := ef.den_term
  inter := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.inter ha hb
    rw [run' _ hm] at run; cases run; exact h v
  diff := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.diff ha hb
    rw [run' _ hm] at run; cases run; exact h v
  empty := fun _ hS _ _ => hS.elim
  inhabited := ef.inhabited
  resp := fun he he' h d => ef.resp he he' h d

/-- Keys of tuple and map literals as Descr builds them: closed literals have negative keys and fewer than 2^31
elements or fields, and open ones other than the top literal have non-negative keys. -/
def KeyOk (t : Term) : Prop := ∀ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] →
  (tag = "closed" → k < 0) ∧ (tag = "open" → l ≠ [] → 0 ≤ k)

/-- Tuple literals of element types, keyed as Descr keys them. -/
def TLit (E : Term → Prop) (t : Term) : Prop := TupleOk E t ∧ KeyOk t

theorem tlit_not : ∀ t, TLit E t → ¬IsTop t := fun _ h => h.1.2

theorem leaf_key_val (l : List Term) (h : Int) :
    Elixir.Module.Types.Descr.«bdd_leaf_key/2» (Term.list l) (.integer h) =
      .ok (.integer (min (l.length : Int) 2147483647 * 134217728 + h)) := by
  have isList : Erlang.erlang.«is_list/1» (Term.list l) = .ok (.atom "true") := by
    cases l <;> simp [Erlang.erlang.«is_list/1», Term.true]
  unfold Elixir.Module.Types.Descr.«bdd_leaf_key/2»
  simp [isList, length_list, Erlang.erlang.«bsl/2», Int.shiftLeft_eq]

theorem tuple3_inj {a b c a' b' c' : Term} (h : Term.tuple #[a, b, c] = Term.tuple #[a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [Term.tuple.injEq] at h
  have := congrArg Array.toList h
  simpa using this

/-- New leaves get the keys Descr gives them. -/
theorem leaf_new_key (t : String) (g : t = "open" ∨ t = "closed") (l : List Term) :
    ∃ k : Int, Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom t) (Term.list l) =
      .ok (.tuple #[.integer k, .atom t, Term.list l]) ∧ KeyOk (.tuple #[.integer k, .atom t, Term.list l]) := by
  have key : ∀ (k : Int), (t = "closed" → k < 0) → (t = "open" → 0 ≤ k) →
      KeyOk (.tuple #[.integer k, .atom t, Term.list l]) := by
    intro k hc ho k' tag l' e
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    have := list_inj e₃
    subst this
    exact ⟨hc, fun o _ => ho o⟩
  rcases g with rfl | rfl
  · obtain ⟨hash, hrun, hlt⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list l))
    exact ⟨min (l.length : Int) 2147483647 * 134217728 + hash,
      by simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, leaf_key_val],
      key _ (fun h => by simp at h) (fun _ => by have := Int.le_min.mpr ⟨Int.natCast_nonneg l.length, (by decide : (0 : Int) ≤ 2147483647)⟩; omega)⟩
  · obtain ⟨hash, hrun, hlt⟩ := Erlang.erlang.phash2_range (Term.list l)
    refine ⟨min (l.length : Int) 2147483647 * 134217728 + hash - 288230376151711744, by
      simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, leaf_key_val, Erlang.erlang.«-/2_integers»],
      key _ (fun _ => ?_) (fun h => by simp at h)⟩
    have := Int.min_le_right (l.length : Int) 2147483647
    omega

theorem sameD_refl (x : Term) : SameD den x x := fun _ => Iff.rfl

theorem exact_pairs (ef : EF nd E V den tl K) : ∀ {a b : List Term}, (∀ e ∈ a, E e) → (∀ e ∈ b, E e) →
    compareExact (fuel (Term.list b) (Term.list a)) (Term.list b) (Term.list a) = .eq → Pairs (SameD den) a b
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h => by simp [Term.list] at h
  | _ :: _, [], _, _, h => by
    have := Lynx.Term.compareExact_eq_symm h
    simp [Term.list] at this
  | x :: a, y :: b, ha, hb, h => by
    rw [Term.list, Term.list, compareExact_cons] at h
    simp only [Ordering.then_eq_eq] at h
    exact ⟨same_of_exact ef (ha x (by simp)) (hb y (by simp)) h.1,
      exact_pairs ef (fun e m => ha e (by simp [m])) (fun e m => hb e (by simp [m])) h.2⟩

/-- `opt_tuple_fuse_elements/4` fuses elements that differ at most at one position, or gives up. -/
theorem fuse_elements_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (n : Int) :
    ∀ (e₁ e₂ acc : List Term), (∀ e ∈ e₁, E e) →
    (∀ e ∈ e₂, E e) → (∀ e ∈ acc, E e) → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4» (D m) (Term.list e₁) (Term.list e₂) (Term.list acc)
        (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ ∃ l, r = Term.list l ∧ (∀ e ∈ l, E e) ∧ l.length = acc.length + e₁.length ∧
        ∀ c v, InT den c l v ↔ InT den c (acc.reverse ++ e₁) v ∨ InT den c (acc.reverse ++ e₂) v) := by
  intro e₁
  induction e₁ with
  | nil =>
    intro e₂ acc _ _ ha
    cases e₂ with
    | nil =>
      refine ⟨Term.list acc.reverse, ?_, Or.inr ⟨acc.reverse, rfl, fun e m => ha e (by simpa using m),
        by simp, fun c v => by simp⟩⟩
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
      simpa [Term.list] using reverse1_list acc
    | cons y ys =>
      refine ⟨_, ?_, Or.inl rfl⟩
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
      simp
  | cons x xs ih =>
    intro e₂ acc h₁ h₂ ha
    cases e₂ with
    | nil =>
      refine ⟨_, ?_, Or.inl rfl⟩
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
      simp
    | cons y ys =>
      have hx : E x := h₁ x (by simp)
      have hy : E y := h₂ y (by simp)
      by_cases same : compareExact (fuel y x) y x = .eq
      · obtain ⟨r, run, out⟩ := ih ys (x :: acc) (fun e m => h₁ e (by simp [m])) (fun e m => h₂ e (by simp [m]))
          (fun e m => by rcases List.mem_cons.mp m with rfl | m; exact hx; exact ha e m)
        refine ⟨r, ?_, ?_⟩
        · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same]
          simpa [Term.list] using run
        · rcases out with rfl | ⟨l, rfl, hl, ll, sl⟩
          · exact Or.inl rfl
          refine Or.inr ⟨l, rfl, hl, by simp [ll]; omega, fun c v => ?_⟩
          rw [sl c v]
          have sd := same_of_exact ef hx hy same
          have pr : Pairs (SameD den) (acc.reverse ++ x :: ys) (acc.reverse ++ y :: ys) :=
            (Pairs.refl sameD_refl _).append ⟨sd, Pairs.refl sameD_refl _⟩
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          rw [inT_same pr]
      · by_cases tails : compareExact (fuel (Term.list ys) (Term.list xs)) (Term.list ys) (Term.list xs) = .eq
        · obtain ⟨f, rf, ef'⟩ := ef.fuse n hx hy (fun h => same (Lynx.Term.compareExact_eq_symm h)) hm
          rcases ef' with rfl | ⟨hu, su⟩
          · refine ⟨_, ?_, Or.inl rfl⟩
            rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
            simp [Erlang.erlang.«=:=/2», same]
            simp [tails, rf]
          · have rev := reverse_list acc (f :: xs)
            refine ⟨_, ?_, Or.inr ⟨acc.reverse ++ f :: xs, rfl, fun e m => ?_, by simp, fun c v => ?_⟩⟩
            · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
              simp [Erlang.erlang.«=:=/2», same]
              simp only [Term.list] at rev
              have nf : Term.compareExact (Term.fuel f (.atom "false")) f (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel f (.atom "nil")) f (.atom "nil") ≠ .eq := by
                rcases ef.static hu with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩ <;> simp
              simp [tails, rf, nf.1, nf.2, rev]
            · simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
              rcases m with m | rfl | m
              · exact ha e m
              · exact hu
              · exact h₁ e (by simp [m])
            · exact union_one_index (Pairs.refl sameD_refl _)
                (exact_pairs ef (fun e m => (h₁ e (by simp [m]))) (fun e m => (h₂ e (by simp [m])))
                  tails) su v
        · refine ⟨_, ?_, Or.inl rfl⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same]
          simp [tails]

/-- A fused leaf, holding the values of both leaves. -/
def FusedLeaf (E : Term → Prop) (den : Term → V → Prop) (t₁ : String) (l₁ : List Term) (t₂ : String) (l₂ : List Term) (r : Term) : Prop :=
  r = .atom "nil" ∨ ∃ (k : Int) (l : List Term), r = .tuple #[.integer k, .atom t₁, Term.list l] ∧
    (∀ e ∈ l, E e) ∧ l.length = l₁.length ∧ KeyOk r ∧ ∀ v, InT den (t₁ == "closed") l v ↔
      InT den (t₁ == "closed") l₁ v ∨ InT den (t₂ == "closed") l₂ v

theorem fuse_leaf_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (k₁ k₂ : Int) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (l₁ l₂ : List Term) (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» (D m) (.tuple #[.integer k₁, .atom t₁, Term.list l₁])
      (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) = .ok r ∧ FusedLeaf E den t₁ l₁ t₂ l₂ r := by
  by_cases same : t₂ = t₁ ∧ l₁.length = l₂.length
  · obtain ⟨rfl, len⟩ := same
    obtain ⟨r, run, out⟩ := fuse_elements_sem ef hm 3 l₁ l₂ [] h₁ h₂ (by simp)
    rcases out with rfl | ⟨l, rfl, hl, ll, sl⟩
    · refine ⟨_, ?_, Or.inl rfl⟩
      unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
      simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», len, Erlang.erlang.«and/2»,
        Term.true]
      simp only [Term.list] at run
      simp [run]
    · obtain ⟨k, hk, key⟩ := leaf_new_key t₂ g₁ l
      have nf : Term.compareExact (Term.fuel (Term.list l) (.atom "false")) (Term.list l) (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel (Term.list l) (.atom "nil")) (Term.list l) (.atom "nil") ≠ .eq := by
        cases l <;> simp [Term.list]
      refine ⟨_, ?_, Or.inr ⟨k, l, rfl, hl, by simpa using ll, key, fun v => by simpa using sl (t₂ == "closed") v⟩⟩
      unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
      simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», len, Erlang.erlang.«and/2»,
        Term.true]
      simp only [Term.list] at run
      simp [run, nf.1, nf.2, hk]
  · refine ⟨_, ?_, Or.inl rfl⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
    by_cases tags : t₂ = t₁
    · subst tags
      have len : ¬(l₁.length : Int) = l₂.length := by simp at same; omega
      simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», len, Erlang.erlang.«and/2»,
        Term.true, Term.false]
    · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», tags, Erlang.erlang.«and/2»,
        Lynx.Except.tryWith, Term.true, Term.false]
      by_cases len : (l₁.length : Int) = l₂.length <;> simp [len]

theorem vT_lit (ef : EF nd E V den tl K) {v : List V} {k : Int} {t : String} {l : List Term} (g : t = "open" ∨ t = "closed")
    (hl : ∀ e ∈ l, E e) :
    valT E den v (.tuple #[.integer k, .atom t, Term.list l]) = Bool.true ↔ InT den (t == "closed") l v := by
  rw [valT_iff ef.semR ⟨k, t, l, rfl, g, hl⟩]
  exact ⟨lit_sem, fun h => ⟨k, t, l, rfl, h⟩⟩

theorem vT_fused (ef : EF nd E V den tl K) {v : List V} {k₁ k₂ k : Int} {t₁ t₂ : String} {l₁ l₂ l : List Term}
    (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed") (h₁ : ∀ e ∈ l₁, E e)
    (h₂ : ∀ e ∈ l₂, E e) (hl : ∀ e ∈ l, E e)
    (sem : ∀ v, InT den (t₁ == "closed") l v ↔ InT den (t₁ == "closed") l₁ v ∨ InT den (t₂ == "closed") l₂ v) :
    valT E den v (.tuple #[.integer k, .atom t₁, Term.list l]) =
      (valT E den v (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) || valT E den v (.tuple #[.integer k₂, .atom t₂, Term.list l₂])) := by
  have e := vT_lit ef (v := v) (k := k) g₁ hl
  have e₁ := vT_lit ef (v := v) (k := k₁) g₁ h₁
  have e₂ := vT_lit ef (v := v) (k := k₂) g₂ h₂
  have s := sem v
  cases a : valT E den v (.tuple #[.integer k, .atom t₁, Term.list l]) <;>
    cases b : valT E den v (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) <;>
    cases c : valT E den v (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) <;> simp_all

/-- What a fusion chain finds: a leaf other than the top literal and the rest of the union. -/
def ChainOk (E : Term → Prop) (den : Term → V → Prop) (ok : Term → Prop) (b leaf r : Term) : Prop :=
  r = .atom "nil" ∨ ∃ fused rest, r = .tuple #[fused, rest] ∧ TLit E fused ∧ Bdd ok rest ∧
    bsize rest < bsize b ∧ ∀ v, (valT E den v fused || eval (valT E den v) rest) = (eval (valT E den v) b || valT E den v leaf)

theorem fuse_current (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {kL : Int} {tL : String} {lL : List Term} (gL : tL = "open" ∨ tL = "closed")
    (hL : ∀ e ∈ lL, E e) {cur : Term} (hc : TLit E cur) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» (D m) cur (.tuple #[.integer kL, .atom tL, Term.list lL]) =
      .ok r ∧ (r = .atom "nil" ∨ (TLit E r ∧ ∀ v, valT E den v r = (valT E den v cur || valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL])))) := by
  obtain ⟨⟨⟨k, t, l, rfl, g, hl⟩, nt⟩, kc⟩ := hc
  obtain ⟨r, run, out⟩ := fuse_leaf_sem ef hm k kL t tL g l lL hl hL
  refine ⟨r, run, ?_⟩
  rcases out with rfl | ⟨k', l', rfl, hl', len, key, sem⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨⟨⟨⟨k', t, l', rfl, g, hl'⟩, fun ⟨k'', e⟩ => nt ⟨.integer k, ?_⟩⟩, key⟩,
      fun v => vT_fused ef g gL hl hL hl' sem⟩
    simp only [Term.tuple.injEq] at e
    have e₁ := congrArg (fun a : Array Term => a[1]?) e
    have e₂ := congrArg (fun a : Array Term => a[2]?) e
    simp [list_eq_nil] at e₁ e₂
    subst e₁ e₂
    cases l with
    | nil => rfl
    | cons _ _ => simp at len

theorem fuse_chain_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {kL : Int} {tL : String} {lL : List Term}
    (gL : tL = "open" ∨ tL = "closed") (hL : ∀ e ∈ lL, E e) :
    ∀ (limit : Nat) (ok : Term → Prop) (b : Term), Bdd ok b → (∀ t, ok t → TLit E t) → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m) b (.tuple #[.integer kL, .atom tL, Term.list lL])
        (.integer (limit : Int)) = .ok r ∧ ChainOk E den ok b (.tuple #[.integer kL, .atom tL, Term.list lL]) r := by
  intro limit
  induction limit with
  | zero =>
    intro ok b _ _
    refine ⟨_, ?_, Or.inl rfl⟩
    rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
    simp
  | succ n ih =>
    intro ok b wb lits
    have nz : ((n + 1 : Nat) : Int) ≠ 0 := by omega
    have nz' : (n : Int) + 1 ≠ 0 := by omega
    have sub : Erlang.erlang.«-/2» (.integer ((n + 1 : Nat) : Int)) (.integer 1) = .ok (.integer (n : Int)) := by
      rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
    have atomCase : ∀ s : String, Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m) (.atom s)
        (.tuple #[.integer kL, .atom tL, Term.list lL]) (.integer ((n + 1 : Nat) : Int)) = .ok (.atom "nil") := by
      intro s
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
      split <;> first | rfl | simp_all
    rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact ⟨_, atomCase _, Or.inl rfl⟩
    · exact ⟨_, atomCase _, Or.inl rfl⟩
    · have hc := lits _ (Bdd.leaf_iff.mp wb)
      obtain ⟨r, run, out⟩ := fuse_current ef hm gL hL hc
      have run' : Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» (D m) (.tuple ⟨[.integer k, x, y]⟩)
          (.tuple #[.integer kL, .atom tL, Term.list lL]) = .ok r := run
      rcases out with rfl | ⟨okr, sr⟩
      · refine ⟨_, ?_, Or.inl rfl⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        simp [nz', run', isMember]
      · have nf : Term.compareExact (Term.fuel r (.atom "false")) r (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel r (.atom "nil")) r (.atom "nil") ≠ .eq := by
          obtain ⟨⟨⟨_, _, _, rfl, -⟩, -⟩, -⟩ := okr
          simp
        refine ⟨_, ?_, Or.inr ⟨r, .atom "bdd_bot", rfl, okr, Bdd.bot, by simp [bsize_atom, bsize_leaf],
          fun v => by simp [sr v, eval]⟩⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        simp [nz', run', isMember, nf.1, nf.2]
    · obtain ⟨isLeaf, okl, hc, hu, hd⟩ := Bdd.node_iff.mp wb
      by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
      · obtain ⟨rfl, rfl⟩ := shape
        have hlit := lits _ okl
        obtain ⟨r, run, out⟩ := fuse_current ef hm gL hL hlit
        rcases out with rfl | ⟨okr, sr⟩
        · obtain ⟨r', run', out'⟩ := ih (Above ok lit) u hu (fun t ht => lits t ht.1)
          rcases out' with rfl | ⟨fused, rest, rfl, okf, wrest, srest, semr⟩
          · refine ⟨_, ?_, Or.inl rfl⟩
            rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
            simp [nz']
            rw [run]
            simp [run']
          · by_cases bot : rest = .atom "bdd_bot"
            · subst bot
              refine ⟨_, ?_, Or.inr ⟨fused, lit, rfl, okf, ?_, ?_, fun v => ?_⟩⟩
              · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
                simp [nz']
                rw [run]
                simp [run']
              · obtain ⟨k', x', y', rfl⟩ := isLeaf
                exact Bdd.leaf_iff.mpr okl
              · obtain ⟨k', x', y', rfl⟩ := isLeaf
                simp [bsize_atom] at srest
                simp [bsize_node, bsize_leaf, bsize_atom]; omega
              · have := semr v
                obtain ⟨k', x', y', rfl⟩ := isLeaf
                simp only [eval] at this ⊢
                revert this
                cases valT E den v fused <;> cases valT E den v (.tuple #[.integer k', x', y']) <;> cases eval (valT E den v) u <;>
                  cases valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL]) <;> simp
            · obtain ⟨hn, runn⟩ := node_new lit (.atom "bdd_top") rest (.atom "bdd_bot") isLeaf (Bdd.top (ok := ok))
                wrest (Bdd.bot (ok := ok))
              refine ⟨_, ?_, Or.inr ⟨fused, .tuple #[.integer hn, lit, .atom "bdd_top", rest, .atom "bdd_bot"], rfl,
                okf, Bdd.node_iff.mpr ⟨isLeaf, okl, Bdd.top, wrest, Bdd.bot⟩, ?_, fun v => ?_⟩⟩
              · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
                simp [nz']
                rw [run]
                simp [run']
                rw [runn]
                rfl
              · simp [bsize_node, bsize_atom] at srest ⊢; omega
              · have := semr v
                simp only [eval] at this ⊢
                revert this
                cases valT E den v fused <;> cases valT E den v lit <;> cases eval (valT E den v) u <;> cases eval (valT E den v) rest <;>
                  cases valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL]) <;> simp
        · have nf : Term.compareExact (Term.fuel r (.atom "false")) r (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel r (.atom "nil")) r (.atom "nil") ≠ .eq := by
            obtain ⟨⟨⟨_, _, _, rfl, -⟩, -⟩, -⟩ := okr
            simp
          refine ⟨_, ?_, Or.inr ⟨r, u, rfl, okr, hu.mono fun t ht => ht.1, by simp [bsize_node, bsize_atom],
            fun v => ?_⟩⟩
          · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
            simp [nz']
            rw [run]
            simp [nf.1, nf.2]
          · simp only [eval, sr v]
            cases valT E den v lit <;> cases eval (valT E den v) u <;> cases valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL]) <;> rfl
      · refine ⟨_, ?_, Or.inl rfl⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        split
        · rename_i e; simp at e; omega
        · rename_i e₁ e₂; simp at e₁; exact absurd ⟨e₁.2.2.1, e₁.2.2.2.2⟩ shape
        · rename_i e₁ e₂; simp at e₁
        · rfl

/-! Optimized unions of tuple types of flat element types. -/

abbrev TField (E : Term → Prop) (x : Term) : Prop := OField (TLit E) x

noncomputable def denTF (E : Term → Prop) (den : Term → V → Prop) (x : Term) (v : List V) : Bool := denO x (valT E den v)

theorem denTF_bdd {x : Term} (wx : Bdd (TLit E) x) (v : List V) : denTF E den x v = eval (valT E den v) x :=
  denO_bdd tlit_not wx _

theorem vT_top (k : Int) (v : List V) : valT E den v (.tuple #[.integer k, .atom "open", .nil]) = Bool.true :=
  valT_true ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩ ⟨k, "open", [], rfl, InT.open_nil v⟩

theorem denTF_top (k : Term) (v : List V) : denTF E den (.tuple #[k, .atom "open", .nil]) v = Bool.true :=
  denO_top k _

theorem denTF_exact {x y : Term} (fx : TField E x) (fy : TField E y) (e : compareExact (fuel y x) y x = .eq) (v : List V) :
    denTF E den y v = denTF E den x v :=
  denO_exact tlit_not fx fy e (valT_resp v)

theorem tuple_union_field {x y : Term} (hx : TField E x) (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok r ∧ TField E r ∧ ∀ v, denTF E den r v = (denTF E den x v || denTF E den y v) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl, Or.inl ⟨k, rfl⟩,
      fun v => by simp [denTF_top]⟩
  rcases hy with ⟨k, rfl⟩ | wy
  · exact ⟨_, tuple_union_right (not_top_of_ok wx tlit_not) _, Or.inl ⟨k, rfl⟩, fun v => by simp [denTF_top]⟩
  obtain ⟨r, hr, okr, semr⟩ := union_ok wx wy
  refine ⟨r, by rw [tuple_union_bdd (not_top_of_ok wx tlit_not) (not_top_of_ok wy tlit_not), hr],
    Or.inr (okr _ wx wy), fun v => ?_⟩
  rw [denTF_bdd (okr _ wx wy), denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]

/-- Leaves of tuple types of element types, including the top literal. -/
def LeafT (E : Term → Prop) (leaf : Term) : Prop :=
  ∃ (k : Int) (t : String) (l : List Term), leaf = .tuple #[.integer k, .atom t, Term.list l] ∧
    (t = "open" ∨ t = "closed") ∧ (∀ e ∈ l, E e) ∧ KeyOk leaf

theorem LeafT.field {leaf : Term} (h : LeafT E leaf) : TField E leaf := by
  obtain ⟨k, t, l, rfl, g, hl, key⟩ := h
  by_cases top : t = "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨k, t, l, rfl, g, hl⟩, fun ⟨k', e⟩ => top ?_⟩, key⟩)
    obtain ⟨-, e₁, e₂⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₁
    exact ⟨e₁, list_eq_nil.mp e₂⟩

theorem LeafT.val {leaf : Term} (h : LeafT E leaf) (v : List V) : denTF E den leaf v = valT E den v leaf := by
  rcases h.field with ⟨k, rfl⟩ | w
  · rw [denTF_top, vT_top]
  · rw [denTF_bdd w]
    obtain ⟨k, t, l, rfl, -⟩ := h
    simp

theorem leafT_of_ok {t : Term} (h : TLit E t) : LeafT E t := by
  obtain ⟨⟨⟨k, tag, l, rfl, g, hl⟩, -⟩, key⟩ := h
  exact ⟨k, tag, l, rfl, g, hl, key⟩

theorem union_leaf_step (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (b leaf : Term) (wb : Bdd (TLit E) b)
    (hleaf : LeafT E leaf)
    (ih : ∀ b' leaf', bsize b' < bsize b → Bdd (TLit E) b' → LeafT E leaf' → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b' leaf' = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (eval (valT E den v) b' || valT E den v leaf')) : ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b leaf = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (eval (valT E den v) b || valT E den v leaf) := by
  have hleaf' := hleaf
  obtain ⟨k, t, l, rfl, g, hl, -⟩ := hleaf
  obtain ⟨c, runc, okc⟩ := fuse_chain_sem ef hm g hl 64 (TLit E) b wb (fun _ h => h)
  have runc' : Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m) b (.tuple #[.integer k, .atom t, Term.list l])
      (.integer 64) = .ok c := by simpa using runc
  rcases okc with rfl | ⟨fused, rest, rfl, okf, wrest, srest, semc⟩
  · obtain ⟨r, hr, fr, sr⟩ := tuple_union_field (Or.inr wb) hleaf'.field
    refine ⟨r, ?_, fr, fun v => by rw [sr v, denTF_bdd wb, hleaf'.val]⟩
    rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
    simp [runc', hr]
  · by_cases bot : rest = .atom "bdd_bot"
    · subst bot
      have wf : Bdd (TLit E) fused := by
        obtain ⟨⟨⟨kf, tf, lf, rfl, gf, hlf⟩, nt⟩, key⟩ := okf
        exact Bdd.leaf_iff.mpr ⟨⟨⟨kf, tf, lf, rfl, gf, hlf⟩, nt⟩, key⟩
      refine ⟨fused, ?_, Or.inr wf, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
        simp [runc']
      · have := semc v
        rw [denTF_bdd wf]
        obtain ⟨⟨⟨kf, _, _, rfl, -⟩, -⟩, -⟩ := okf
        simpa [eval] using this
    · obtain ⟨r, hr, fr, sr⟩ := ih rest fused srest wrest (leafT_of_ok okf)
      refine ⟨r, ?_, fr, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
        simp [runc', hr]
      · rw [sr v, ← semc v]
        cases valT E den v fused <;> cases eval (valT E den v) rest <;> rfl

/-- `opt_tuple_union_leaf/2` adds a leaf to a union, fusing it with the leaves it can. -/
theorem union_leaf_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (n : Nat) (b leaf : Term), bsize b ≤ n →
    Bdd (TLit E) b → LeafT E leaf → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b leaf = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (eval (valT E den v) b || valT E den v leaf) := by
  intro n
  induction n with
  | zero =>
    intro b leaf sz wb hl
    exact union_leaf_step ef hm b leaf wb hl fun b' _ lt => by omega
  | succ n ih =>
    intro b leaf sz wb hl
    exact union_leaf_step ef hm b leaf wb hl fun b' leaf' lt wb' hl' => ih b' leaf' (by omega) wb' hl'

theorem TField.shape {x : Term} (h : TField E x) :
    x = .atom "bdd_top" ∨ x = .atom "bdd_bot" ∨ LeafT E x ∨
      (∃ (hh : Int) (lit c u d : Term), x = .tuple #[.integer hh, lit, c, u, d] ∧ Bdd (TLit E) x) := by
  rcases h with ⟨k, rfl⟩ | w
  · refine Or.inr (Or.inr (Or.inl ⟨k, "open", [], rfl, Or.inl rfl, by simp, fun k' tag l' e => ?_⟩))
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₂
    subst e₂
    exact ⟨fun h => by simp at h, fun _ ne => absurd (list_eq_nil.mp e₃.symm) ne⟩
  rcases w.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨hh, lit, c, u, d, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl (leafT_of_ok (Bdd.leaf_iff.mp w))))
  · exact Or.inr (Or.inr (Or.inr ⟨hh, lit, c, u, d, rfl, w⟩))

theorem via_tuple_union {m : Nat} {x y : Term} (hx : TField E x) (hy : TField E y)
    (e : Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = Elixir.Module.Types.Descr.«tuple_union/2» x y) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v || denTF E den y v) := by
  obtain ⟨r, hr, fr, sr⟩ := tuple_union_field hx hy
  exact ⟨r, by rw [e, hr], fr, sr⟩

/-- Optimized unions of tuple types of element types hold the tuples of either. -/
theorem opt_tuple_union_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {x y : Term} (hx : TField E x)
    (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v || denTF E den y v) := by
  have leafNode : ∀ {a b : Term}, LeafT E a → Bdd (TLit E) b → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b a = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (denTF E den b v || denTF E den a v) := by
    intro a b ha wb
    obtain ⟨r, hr, fr, sr⟩ := union_leaf_sem ef (m := m) hm _ b a (Nat.le_refl _) wb ha
    exact ⟨r, hr, fr, fun v => by rw [sr v, denTF_bdd wb, ha.val]⟩
  rcases hx.shape with rfl | rfl | ⟨k₁, t₁, l₁, rfl, g₁, h₁, key₁⟩ | ⟨h₁, a₁, c₁, u₁, d₁, rfl, w₁⟩ <;>
    rcases hy.shape with rfl | rfl | ⟨k₂, t₂, l₂, rfl, g₂, h₂, key₂⟩ | ⟨h₂, a₂, c₂, u₂, d₂, rfl, w₂⟩
  all_goals first
    | exact via_tuple_union hx hy (by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; rfl)
    | (apply via_tuple_union hx hy
       unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
       simp only [leaf_guard, node_ne3, ite_false]
       done)
    | skip
  · by_cases same : compareExact (fuel (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) (.tuple #[.integer k₁, .atom t₁, Term.list l₁])) (.tuple #[.integer k₂, .atom t₂, Term.list l₂])
        (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) = .eq
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp only [leaf_guard, ite_eq_left same]; rfl,
        hx, fun v => by rw [denTF_exact hx hy same, Bool.or_self]⟩
    have lx : LeafT E (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) := ⟨k₁, t₁, l₁, rfl, g₁, h₁, key₁⟩
    have ly : LeafT E (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) := ⟨k₂, t₂, l₂, rfl, g₂, h₂, key₂⟩
    have e₁ := fun v => vT_lit ef (v := v) (k := k₁) g₁ h₁
    have e₂ := fun v => vT_lit ef (v := v) (k := k₂) g₂ h₂
    obtain ⟨res, run, sok⟩ := strategy_sem ef hm t₁ t₂ g₁ g₂ l₁ l₂ h₁ h₂
    have form := strategy_form ef hm t₁ t₂ g₁ g₂ l₁ l₂ h₁ h₂ run
    rcases form with rfl | ⟨j, d₁, d₂, rfl⟩ | rfl | rfl | rfl
    · exact absurd rfl sok.1
    · obtain ⟨rfl, a₁, b₁, a₂, b₂, rfl, rfl, rfl, pa, pb, nd⟩ := sok.2.1 _ _ _ rfl
      have hd₁ : E d₁ := h₁ d₁ (by simp)
      have hd₂ : E d₂ := h₂ d₂ (by simp)
      obtain ⟨u₀, hu₀, ru₀, su₀, -⟩ := ef.union hd₁ hd₂
      obtain ⟨f, rf, out⟩ := ef.fuse 3 hd₁ hd₂ nd hm
      -- the fused element, or the union when fusing fails
      obtain ⟨u, hu, su, hcase⟩ : ∃ u, E u ∧ (∀ v, den u v ↔ den d₁ v ∨ den d₂ v) ∧
          ((f = .atom "nil" ∧ u = u₀) ∨
            (u = f ∧ Term.compareExact (Term.fuel f (.atom "false")) f (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel f (.atom "nil")) f (.atom "nil") ≠ .eq)) := by
        rcases out with rfl | ⟨hf, sf⟩
        · exact ⟨u₀, hu₀, su₀, Or.inl ⟨rfl, rfl⟩⟩
        · have nf : Term.compareExact (Term.fuel f (.atom "false")) f (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel f (.atom "nil")) f (.atom "nil") ≠ .eq := by
            rcases ef.static hf with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩ <;> simp
          exact ⟨f, hf, sf, Or.inr ⟨rfl, nf⟩⟩
      have elems : ∀ e ∈ a₁ ++ u :: b₁, E e := by
        intro e me
        simp only [List.mem_append, List.mem_cons] at me
        rcases me with me | rfl | me
        · exact h₁ e (by simp [me])
        · exact hu
        · exact h₁ e (by simp [me])
      have rep := replace_list (a₁ ++ d₁ :: b₁) a₁.length u (by simp)
      rw [set_mid] at rep
      obtain ⟨k, hk, key⟩ := leaf_new_key t₁ g₁ (a₁ ++ u :: b₁)
      have hres : LeafT E (Term.tuple #[Term.integer k, Term.atom t₁, Term.list (a₁ ++ u :: b₁)]) := ⟨k, t₁, _, rfl, g₁, elems, key⟩
      refine ⟨_, ?_, hres.field, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
        simp only [run, Lynx.Except.ok_bind]
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, nf⟩
        · simp [isMember, rf, ru₀ m hm, rep, hk, Erlang.erlang.«=:=/2», same]
        · simp [isMember, rf, nf.1, nf.2, rep, hk, Erlang.erlang.«=:=/2», same]
      · apply Bool.eq_iff_iff.mpr
        rw [hres.val, lx.val, ly.val, vT_lit ef g₁ elems, Bool.or_eq_true, e₁ v, e₂ v]
        exact union_one_index pa pb su v
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp [Erlang.erlang.«=:=/2», same, run], ly.field, fun v => ?_⟩
      rw [lx.val, ly.val]
      by_cases hx' : valT E den v (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) = Bool.true
      · rw [hx', (e₂ v).mpr (sok.2.2.1 rfl v ((e₁ v).mp hx'))]; rfl
      · simp only [Bool.not_eq_true] at hx'; rw [hx']; rfl
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp [Erlang.erlang.«=:=/2», same, run], lx.field, fun v => ?_⟩
      rw [lx.val, ly.val]
      by_cases hy' : valT E den v (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) = Bool.true
      · rw [hy', (e₁ v).mpr (sok.2.2.2 rfl v ((e₂ v).mp hy'))]; rfl
      · simp only [Bool.not_eq_true] at hy'; rw [hy', Bool.or_false]
    · have o₁ : ¬(t₁ = "open" ∧ l₁ = []) := fun h => strategy_top_none (D m) t₁ t₂ g₁ g₂ l₁ l₂ (Or.inl h) run
      have o₂ : ¬(t₂ = "open" ∧ l₂ = []) := fun h => strategy_top_none (D m) t₁ t₂ g₁ g₂ l₁ l₂ (Or.inr h) run
      have notTop : ∀ {leaf : Term} {k : Int} {t : String} {l : List Term}, leaf = .tuple #[.integer k, .atom t, Term.list l] →
          ¬(t = "open" ∧ l = []) → LeafT E leaf → Bdd (TLit E) leaf := by
        intro leaf k t l e o hl
        rcases hl.field with ⟨k', e'⟩ | w
        · subst e
          obtain ⟨-, e₂, e₃⟩ := tuple3_inj e'
          simp only [Term.atom.injEq] at e₂
          exact absurd ⟨e₂, list_eq_nil.mp e₃⟩ o
        · exact w
      have w₁ := notTop rfl o₁ lx
      have w₂ := notTop rfl o₂ ly
      obtain ⟨r, hr, okr, semr⟩ := union_ok w₁ w₂
      refine ⟨r, ?_, Or.inr (okr _ w₁ w₂), fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, hr]
      · rw [denTF_bdd (okr _ w₁ w₂), denTF_bdd w₁, denTF_bdd w₂, semr _ (valT_resp v)]
  · obtain ⟨r, hr, fr, sr⟩ := leafNode ⟨k₁, t₁, l₁, rfl, g₁, h₁, key₁⟩ w₂
    refine ⟨r, ?_, fr, fun v => by rw [sr v, Bool.or_comm]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [leaf_guard, node_ne3, ite_false]
    exact hr
  · obtain ⟨r, hr, fr, sr⟩ := leafNode ⟨k₂, t₂, l₂, rfl, g₂, h₂, key₂⟩ w₁
    refine ⟨r, ?_, fr, sr⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only []
    exact hr

end Elixir.STTDescrProofsTest.Nest
