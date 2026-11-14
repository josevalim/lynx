namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem vT_closed_nil (ef : EF nd E V den tl K) (v : List V) (k : Int) :
    valT E den v (.tuple #[.integer k, .atom "closed", .nil]) = decide (v = []) := by
  have := vT_lit ef (v := v) (k := k) (t := "closed") (l := []) (Or.inr rfl) (by simp)
  simp only [Term.list] at this
  cases h : valT E den v (.tuple #[.integer k, .atom "closed", .nil]) <;> cases v <;> simp_all [InT]

theorem vT_open_term (ef : EF nd E V den tl K) (v : List V) (k : Int) :
    valT E den v (.tuple #[.integer k, .atom "open", Term.list [.atom "term"]]) = !decide (v = []) := by
  have := vT_lit ef (v := v) (k := k) (t := "open") (l := [.atom "term"]) (Or.inl rfl)
    (by simpa using ef.term)
  cases h : valT E den v (.tuple #[.integer k, .atom "open", Term.list [.atom "term"]]) <;> cases v <;>
    simp_all [InT, ef.den_term, InT.open_nil]

/-! Optimized differences of tuple types on tuples of values. -/

/-- Element types that include, position by position, those of another list, as far as both go. -/
def ZipSub (den : Term → V → Prop) : List Term → List Term → Prop
  | a :: as, b :: bs => (∀ x, den a x → den b x) ∧ ZipSub den as bs
  | _, _ => True

/-- Element types that share no value at some position of both lists. -/
def ZipDisj (den : Term → V → Prop) : List Term → List Term → Prop
  | a :: as, b :: bs => (∀ x, den a x → den b x → False) ∨ ZipDisj den as bs
  | _, _ => False

theorem zipDisj_sem {c₁ c₂ : Bool} : ∀ {l₁ l₂ : List Term} {v : List V}, ZipDisj den l₁ l₂ →
    InT den c₁ l₁ v → InT den c₂ l₂ v → False
  | a :: as, b :: bs, x :: xs, h, h₁, h₂ => by
    rcases h with h | h
    · exact h x h₁.1 h₂.1
    · exact zipDisj_sem h h₁.2 h₂.2
  | [], _, _, h, _, _ => by cases h
  | _ :: _, [], _, h, _, _ => by cases h
  | _ :: _, _ :: _, [], _, h₁, _ => h₁.elim

theorem zipSub_sem : ∀ {l₁ l₂ : List Term} {v : List V}, ZipSub den l₁ l₂ → l₂.length ≤ l₁.length →
    InT den Bool.false l₁ v → InT den Bool.false l₂ v
  | _, [], _, _, _, _ => InT.open_nil _
  | a :: as, b :: bs, x :: xs, h, le, h₁ => ⟨h.1 x h₁.1, zipSub_sem h.2 (by simp at le; omega) h₁.2⟩
  | [], _ :: _, _, _, le, _ => by simp at le
  | _ :: _, _ :: _, [], _, _, h₁ => h₁.elim

/-- The walk of `opt_tuple_leaf_difference/3` over elements. -/
theorem tld_walk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (l₁ : List Term), (∀ e ∈ l₁, E e) → ∀ (l₂ : List Term),
    (∀ e ∈ l₂, E e) → ∀ s : Bool, ∃ res,
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D m) (Term.list l₁) (Term.list l₂) (boolAtom s) =
        .ok res ∧ ((res = .atom "disjoint" ∧ ZipDisj den l₁ l₂) ∨
          (res = .atom "subtype" ∧ s = Bool.true ∧ ZipSub den l₁ l₂) ∨
        res = .atom "none") := by
  have last : ∀ l₁ l₂ : List Term, (l₁ = [] ∨ l₂ = []) → ∀ s : Bool, ∃ res,
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D m) (Term.list l₁) (Term.list l₂) (boolAtom s) =
        .ok res ∧ ((res = .atom "disjoint" ∧ ZipDisj den l₁ l₂) ∨
          (res = .atom "subtype" ∧ s = Bool.true ∧ ZipSub den l₁ l₂) ∨
        res = .atom "none") := by
    intro l₁ l₂ e s
    have zs : ZipSub den l₁ l₂ := by cases l₁ <;> cases l₂ <;> simp_all [ZipSub]
    cases s
    · refine ⟨.atom "none", ?_, Or.inr (Or.inr rfl)⟩
      rcases e with rfl | rfl
      · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
        simp [boolAtom, isMember]
      · cases l₁ <;> rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def] <;>
          simp [boolAtom, isMember]
    · refine ⟨.atom "subtype", ?_, Or.inr (Or.inl ⟨rfl, rfl, zs⟩)⟩
      rcases e with rfl | rfl
      · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
        simp [boolAtom, isMember]
      · cases l₁ <;> rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def] <;>
          simp [boolAtom, isMember]
  intro l₁
  induction l₁ with
  | nil => intro _ l₂ _ s; exact last [] l₂ (Or.inl rfl) s
  | cons a as ih =>
    intro h₁ l₂ h₂ s
    cases l₂ with
    | nil => exact last _ [] (Or.inr rfl) s
    | cons b bs =>
      have ha := h₁ a List.mem_cons_self
      have hb := h₂ b List.mem_cons_self
      obtain ⟨bd, hd, sd⟩ := ef.disj ha hb
      obtain ⟨bs', hs, ss⟩ := ef.sub ha hb
      have rd := hd m hm
      have rs := hs m hm
      cases bd
      · cases s
        · refine ⟨.atom "none", ?_, Or.inr (Or.inr rfl)⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
          simp [boolAtom, Lynx.Except.andAlso, rd, Erlang.erlang.«/=/2»]
        · cases bs'
          · refine ⟨.atom "none", ?_, Or.inr (Or.inr rfl)⟩
            rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
            simp [boolAtom, Lynx.Except.andAlso, rd, rs, Erlang.erlang.«/=/2»]
          · obtain ⟨res, run, sem⟩ := ih (fun e m' => h₁ e (List.mem_cons_of_mem _ m')) bs
              (fun e m' => h₂ e (List.mem_cons_of_mem _ m')) Bool.true
            refine ⟨res, ?_, ?_⟩
            · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
              simp [boolAtom] at run
              simp [boolAtom, Lynx.Except.andAlso, rd, rs, Erlang.erlang.«/=/2», run]
            · rcases sem with ⟨e, d⟩ | ⟨e, -, sb⟩ | e
              · exact Or.inl ⟨e, Or.inr d⟩
              · exact Or.inr (Or.inl ⟨e, rfl, ss rfl, sb⟩)
              · exact Or.inr (Or.inr e)
      · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, Or.inl (sd rfl)⟩⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
        simp [boolAtom, Lynx.Except.andAlso, rd, Erlang.erlang.«/=/2»]

theorem strategy_lsr (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    (n₁ n₂ : Nat) (h : Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
      (.integer n₂) = .ok (.atom "left_subtype_of_right")) :
    (t₂ = "closed" → t₁ = "closed" ∧ n₁ = n₂) ∧ n₂ ≤ n₁ := by
  unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» at h
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> rcases Nat.lt_trichotomy n₁ n₂ with c | c | c <;>
    simp [Erlang.erlang.«/=/2», Erlang.erlang.«==/2», c, Int.compare_eq_lt,
      Int.compare_eq_gt, Erlang.erlang.«>=/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Int.isGE_compare] at h ⊢ <;>
    first
      | omega
      | (have h3 : (n₁ : Int) ≠ n₂ := by omega
         simp [h3] at h)
      | (have h1 : ¬n₂ < n₁ := by omega
         simp [h1] at h)

/-- Tuple values. -/
def ValT (E : Term → Prop) (den : Term → V → Prop) (ρ : Term → Bool) : Prop := ∃ v, ρ = valT E den v

theorem valT_respT : ∀ ρ, ValT E den ρ → Resp ρ := fun _ ⟨v, e⟩ => e ▸ valT_resp v

/-- `opt_tuple_leaf_difference/3` compares tuple literals soundly. -/
theorem tuple_cmp (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a₁ a₂ type : Term) (h₁ : TLit E a₁) (h₂ : TLit E a₂) :
    ∃ res, (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "opt_tuple_leaf_difference" 3 #[])
      #[a₁, a₂, type] = .ok res ∧ CmpOk (ValT E den) (TLit E) a₁ a₂ type res := by
  obtain ⟨⟨⟨k₁, t₁, l₁, rfl, g₁, e₁⟩, -⟩, -⟩ := h₁
  obtain ⟨⟨⟨k₂, t₂, l₂, rfl, g₂, e₂⟩, -⟩, -⟩ := h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:opt_tuple_leaf_difference/3».pure]
  obtain ⟨sv, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨v, e⟩ => ?_⟩⟩
    · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
      simp [length_list, hv, disj.mpr d]
    · subst e
      apply Bool.eq_false_iff.mpr
      intro h
      rw [Bool.and_eq_true, vT_lit ef g₁ e₁, vT_lit ef g₂ e₂] at h
      obtain ⟨hw, hlw⟩ := h
      rw [InT.iff_open] at hw hlw
      rcases d with ⟨rfl, rfl, ne⟩ | ⟨rfl, rfl, lt⟩ | ⟨rfl, rfl, lt⟩
      · exact ne (by rw [← hw.2 rfl, hlw.2 rfl])
      · have := hlw.1.length_le; have := hw.2 rfl; omega
      · have := hw.1.length_le; have := hlw.2 rfl; omega
  have nv : sv ≠ .atom "disjoint" := fun e => d (disj.mp e)
  have step : ∀ s : Bool, (s = Bool.true ↔ sv = .atom "left_subtype_of_right") →
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D n) (.tuple #[.integer k₁, .atom t₁, Term.list l₁])
        (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) type =
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D n) (Term.list l₁) (Term.list l₂) (boolAtom s) := by
    intro s hs
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp only [length_list, Lynx.Except.ok_bind, hv]
    cases s
    · have : sv ≠ .atom "left_subtype_of_right" := fun e => by simpa using hs.mpr e
      have eq : Erlang.erlang.«==/2» sv (.atom "left_subtype_of_right") = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2», this]
      rw [eq]; rfl
    · have := hs.mp rfl
      subst this
      have eq : Erlang.erlang.«==/2» (.atom "left_subtype_of_right") (.atom "left_subtype_of_right") =
          .ok (.atom "true") := by simp [Erlang.erlang.«==/2»]
      rw [eq]; rfl
  classical
  obtain ⟨res, run, sem⟩ := tld_walk ef hn l₁ e₁ l₂ e₂ (decide (sv = .atom "left_subtype_of_right"))
  refine ⟨res, by rw [step _ decide_eq_true_iff, run], ?_⟩
  rcases sem with ⟨rfl, zd⟩ | ⟨rfl, ls, zs⟩ | rfl
  · refine Or.inl ⟨rfl, fun ρ ⟨v, e⟩ => ?_⟩
    subst e
    apply Bool.eq_false_iff.mpr
    intro h
    rw [Bool.and_eq_true, vT_lit ef g₁ e₁, vT_lit ef g₂ e₂] at h
    exact zipDisj_sem zd h.1 h.2
  · simp only [decide_eq_true_eq] at ls
    subst ls
    obtain ⟨cl, le⟩ := strategy_lsr t₁ t₂ g₁ g₂ _ _ hv
    refine Or.inr (Or.inl ⟨rfl, fun ρ ⟨v, e⟩ h => ?_⟩)
    subst e
    rw [vT_lit ef g₁ e₁] at h
    rw [vT_lit ef g₂ e₂, InT.iff_open]
    rw [InT.iff_open] at h
    refine ⟨zipSub_sem zs le h.1, fun c => ?_⟩
    obtain ⟨c₁, len⟩ := cl (by simpa using c)
    rw [h.2 (by simp [c₁]), len]
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! Differences of tuple types on tuples of values. -/

theorem denTF_bot (v : List V) : denTF E den (.atom "bdd_bot") v = Bool.false := by
  rw [denTF_bdd (Bdd.bot (ok := TLit E))]; rfl

/-- Open leaves other than the top tuple hold no empty tuple. -/
theorem open_leaf_ne (ef : EF nd E V den tl K) {kx e : Term} (wx : Bdd (TLit E) (.tuple #[kx, .atom "open", e])) (v : List V)
    (h : denTF E den (.tuple #[kx, .atom "open", e]) v = Bool.true) : v ≠ [] := by
  obtain ⟨kx, rfl⟩ := leaf_int wx
  have okx := Bdd.leaf_iff.mp wx
  obtain ⟨⟨⟨k, t, l, eq, g, hl⟩, nt⟩, -⟩ := okx
  obtain ⟨e₀, e₁, e₂⟩ := tuple3_inj eq
  simp only [Term.atom.injEq, Term.integer.injEq] at e₀ e₁
  subst e₀ e₁ e₂
  rw [denTF_bdd wx, eval_leaf, vT_lit ef g hl] at h
  have ne : l ≠ [] := fun h => nt ⟨_, by rw [h]⟩
  intro hv
  subst hv
  cases l with
  | nil => exact ne rfl
  | cons _ _ => exact h.elim

/-- Plain differences of tuple types hold the tuples of the first and not the second. -/
theorem tuple_diff_val (ef : EF nd E V den tl K) {x y : Term} (fx : TField E x) (fy : TField E y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧ TField E w ∧
      ∀ v, denTF E den w v = (denTF E den x v && !denTF E den y v) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, Or.inr Bdd.bot,
      fun v => by rw [denTF_bot, denTF_top]; simp⟩
  have ny := not_top_of_ok wy tlit_not
  by_cases special : ∃ k, y = .tuple #[k, .atom "closed", .nil]
  · obtain ⟨k, rfl⟩ := special
    rcases fx with ⟨kt, rfl⟩ | wx
    · obtain ⟨h, run, key⟩ := leaf_new_key "open" (Or.inl rfl) [.atom "term"]
      have lit : LeafT E (.tuple #[.integer h, .atom "open", Term.list [.atom "term"]]) :=
        ⟨h, "open", [.atom "term"], rfl, Or.inl rfl, fun e me => by rw [List.mem_singleton.mp me]; exact ef.term, key⟩
      obtain ⟨k, rfl⟩ := leaf_int wy
      refine ⟨_, by simp [Elixir.Module.Types.Descr.«tuple_difference/2», Erlang.erlang.«==/2», run], lit.field,
        fun v => ?_⟩
      rw [lit.val, denTF_top, denTF_bdd wy, eval_leaf, vT_open_term ef, vT_closed_nil ef]
      simp
    · by_cases openLeaf : ∃ kx e, x = .tuple #[kx, .atom "open", e]
      · obtain ⟨kx, e, rfl⟩ := openLeaf
        have ne : e ≠ .nil := fun h => not_top_of_ok wx tlit_not _ (by rw [h])
        refine ⟨_, ?_, Or.inr wx, fun v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          cases e <;> simp_all [Erlang.erlang.«==/2»]
        · obtain ⟨k, rfl⟩ := leaf_int wy
          cases hx : denTF E den (.tuple #[kx, .atom "open", e]) v
          · rfl
          · have := open_leaf_ne ef wx v hx
            rw [denTF_bdd wy, eval_leaf, vT_closed_nil ef]
            simp [this]
      · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
        have ww := keep _ wx wy
        refine ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨h, _⟩ => openLeaf h), run],
          Or.inr ww, fun v => ?_⟩
        rw [denTF_bdd ww, denTF_bdd wx, denTF_bdd wy, sem _ (valT_resp v)]
  · rcases fx with ⟨kt, rfl⟩ | wx
    · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_top]
        · rw [denTF_bot, denTF_bdd wy]; rfl
      · refine ⟨_, ?_, Or.inl ⟨kt, rfl⟩, fun v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_bot]
        · rw [denTF_bdd wy]; simp
      all_goals
        obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        have ww := keep _ wy
        refine ⟨w, by rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run], Or.inr ww, fun v => ?_⟩
        rw [denTF_bdd ww, denTF_bdd wy, denTF_top, sem _ (valT_resp v)]
        simp
    · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
      have ww := keep _ wx wy
      refine ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨_, h⟩ => special h), run],
        Or.inr ww, fun v => ?_⟩
      rw [denTF_bdd ww, denTF_bdd wx, denTF_bdd wy, sem _ (valT_resp v)]

/-- `opt_tuple_difference/2` is `tuple_difference/2`, but on the leaves it compares, and exactly equal leaves leave
nothing. -/
theorem opt_tuple_split (d : Dispatcher) (x y : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_difference/2» d x y = Elixir.Module.Types.Descr.«tuple_difference/2» x y ∨
    (Elixir.Module.Types.Descr.«opt_tuple_difference/2» d x y = Elixir.Module.Types.Descr.«bdd_difference/3» d x y
        (.function "Elixir.Module.Types.Descr" "opt_tuple_leaf_difference" 3 #[]) ∧
      Elixir.Module.Types.Descr.«tuple_difference/2» x y = Elixir.Module.Types.Descr.«bdd_difference/2» x y ∧
      (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) ∧
      ((∀ k, x ≠ .tuple #[k, .atom "open", .nil]) ∨ ∀ arr, y ≠ .tuple arr)) ∨
    (∃ k a b, x = .tuple #[k, a, b] ∧ compareExact (fuel y x) y x = .eq ∧
      Elixir.Module.Types.Descr.«opt_tuple_difference/2» d x y = .ok (.atom "bdd_bot")) := by
  by_cases same : (∃ k a b, x = .tuple #[k, a, b] ∧ compareExact (fuel y x) y x = .eq) ∧ ∀ k, y ≠ .tuple #[k, .atom "open", .nil]
  · obtain ⟨⟨k, a, b, rfl, e⟩, ny⟩ := same
    right; right
    refine ⟨k, a, b, rfl, e, ?_⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2»
    split
    all_goals first
      | rfl
      | exact (ny _ rfl).elim
      | (simp only [leaf_guard]; rw [ite_eq_left (by simpa using e)]; rfl)
  unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2»
  split
  · left; unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl
  rename_i h₁
  simp only [leaf_guard]
  have xopen : ∀ (h₃ : ∀ k arr, x = .tuple #[k, .atom "open", .nil] → y = .tuple arr → False),
      (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) ∨ ∀ arr, y ≠ .tuple arr := by
    intro h₃
    by_cases hx : ∃ k, x = .tuple #[k, .atom "open", .nil]
    · obtain ⟨k, e⟩ := hx
      exact Or.inr fun arr e' => h₃ _ _ e e'
    · exact Or.inl fun k e => hx ⟨k, e⟩
  split
  · rw [ite_eq_right (fun e => same ⟨⟨_, _, _, rfl, e⟩, fun k e' => h₁ k e'⟩)]
    split
    · left; rename_i heq; rw [heq]; unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      first | rfl | (split <;> simp_all)
    · left; rename_i heq; rw [heq]; unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      first | rfl | (split <;> simp_all)
    · rename_i h₂ h₃
      refine Or.inr (Or.inl ⟨rfl, ?_, fun k e => h₁ _ e, xopen fun k arr e e' => h₃ _ _ e e'⟩)
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split <;> simp_all
  · split
    · left; unfold Elixir.Module.Types.Descr.«tuple_difference/2»; first | rfl | (split <;> simp_all)
    · left; unfold Elixir.Module.Types.Descr.«tuple_difference/2»; first | rfl | (split <;> simp_all)
    · rename_i h₂ h₃
      refine Or.inr (Or.inl ⟨rfl, ?_, fun k e => h₁ _ e, xopen fun k arr e e' => h₃ _ _ e e'⟩)
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split <;> simp_all

/-- Optimized differences of tuple types hold the tuples of the first and not the second. -/
theorem opt_tuple_diff_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {x y : Term} (fx : TField E x) (fy : TField E y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_difference/2» (D (n + 1)) x y = .ok w ∧ TField E w ∧
      ∀ v, denTF E den w v = (denTF E den x v && !denTF E den y v) := by
  obtain ⟨w, run, fw, sem⟩ := tuple_diff_val ef fx fy
  rcases opt_tuple_split (D (n + 1)) x y with e | ⟨e, eb, ny, nx⟩ | ⟨k, a, b, rfl, same, e⟩
  · exact ⟨w, by rw [e, run], fw, sem⟩
  rotate_left
  · exact ⟨_, e, Or.inr Bdd.bot, fun v => by rw [denTF_exact fx fy same, Bool.and_not_self, denTF_bot]⟩
  rw [e]
  have wy : Bdd (TLit E) y := by
    rcases fy with ⟨k, rfl⟩ | wy
    · exact absurd rfl (ny _)
    · exact wy
  rcases fx with ⟨k, rfl⟩ | wx
  · rcases nx with nx | nx
    · exact absurd rfl (nx _)
    have wx : Bdd (TupleLit E) (.tuple #[.integer k, .atom "open", .nil]) :=
      Bdd.leaf_iff.mpr ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
    rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
  obtain ⟨r, hr, okr, semr⟩ := diff3_ok valT_respT (fun a₁ a₂ type _ h₁ h₂ => tuple_cmp ef hn a₁ a₂ type h₁ h₂)
    _ y wy (fun _ h => h) x wx
  refine ⟨r, hr, Or.inr okr, fun v => ?_⟩
  rw [denTF_bdd okr, denTF_bdd wx, denTF_bdd wy, semr _ ⟨v, rfl⟩]

end Elixir.STTDescrProofsTest.Nest
