namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of tuple literals of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

def SameD (den : Term → V → Prop) (x y : Term) : Prop := ∀ v, den x v ↔ den y v
def SubD (den : Term → V → Prop) (x y : Term) : Prop := ∀ v, den x v → den y v

/-- What the status of a walk over the elements of two tuple literals says about the walked elements. -/
def StatusInv (den : Term → V → Prop) (status : Term) (p₁ p₂ : List Term) : Prop :=
  (status = .atom "all_equal" ∧ Pairs (SameD den) p₁ p₂) ∨
  (∃ (j : Nat) (d₁ d₂ : Term) (a₁ b₁ a₂ b₂ : List Term),
    status = Term.tuple #[Term.atom "one_index_difference", Term.integer j, d₁, d₂] ∧ p₁ = a₁ ++ d₁ :: b₁ ∧ p₂ = a₂ ++ d₂ :: b₂ ∧
    a₁.length = j ∧ Pairs (SameD den) a₁ a₂ ∧ Pairs (SameD den) b₁ b₂ ∧ compareExact (fuel d₁ d₂) d₁ d₂ ≠ .eq) ∨
  (status = .atom "left_subtype_of_right" ∧ Pairs (SubD den) p₁ p₂) ∨
  (status = .atom "right_subtype_of_left" ∧ Pairs (SubD den) p₂ p₁)

theorem StatusInv.endSt {st : Term} {p₁ p₂ : List Term} (h : StatusInv den st p₁ p₂) :
    StatusInv den (endSt st) p₁ p₂ := by
  rcases h with ⟨rfl, pr⟩ | h | h | h
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, pr.mono fun _ _ h v => (h v).mp⟩))
  · have h' := h
    obtain ⟨_, _, _, _, _, _, _, rfl, -⟩ := h'
    rw [endSt_of_ne (by simp)]; exact Or.inr (Or.inl h)
  · rw [endSt_of_ne (by rw [h.1]; simp)]; exact Or.inr (Or.inr (Or.inl h))
  · rw [endSt_of_ne (by rw [h.1]; simp)]; exact Or.inr (Or.inr (Or.inr h))

theorem same_of_exact (ef : EF nd E V den tl K) {x y : Term} (hx : E x) (hy : E y) (h : compareExact (fuel y x) y x = .eq) : (SameD den) x y := by
  have c := compare_eq_of_compareExact_eq _ _ h
  exact fun v => ⟨fun d => ef.resp hy hx c d, fun d => ef.resp hx hy (Lynx.Term.compare_eq_symm c) d⟩

theorem sub_bool (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {a b : Term} (ha : E a) (hb : E b) :
    ∃ s : Bool, Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧ (s = Bool.true → (SubD den) a b) := by
  obtain ⟨s, hs, sound⟩ := ef.sub ha hb
  exact ⟨s, hs m hm, sound⟩

/-- The walk of `opt_tuple_union_strategy_index/4` over the elements of two tuple literals. -/
theorem walk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (r₁ r₂ p₁ p₂ : List Term) (status : Term), (∀ e ∈ r₁, E e) →
    (∀ e ∈ r₂, E e) → (∀ e ∈ p₁, E e) → (∀ e ∈ p₂, E e) → p₁.length = p₂.length →
    StatusInv den status p₁ p₂ → ∃ res,
      Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m) (Term.list r₁) (Term.list r₂)
        (.integer (p₁.length : Int)) status = .ok res ∧
      (res = Term.atom "none" ∨ ∃ c₁ s₁ c₂ s₂, r₁ = c₁ ++ s₁ ∧ r₂ = c₂ ++ s₂ ∧ c₁.length = c₂.length ∧
        (s₁ = [] ∨ s₂ = []) ∧ StatusInv den res (p₁ ++ c₁) (p₂ ++ c₂)) ∧
      (status = .atom "left_subtype_of_right" ∨ status = .atom "right_subtype_of_left" →
        res = status ∨ res = .atom "none") ∧ res ≠ .atom "all_equal" := by
  intro r₁
  induction r₁ with
  | nil =>
    intro r₂ p₁ p₂ status _ _ _ _ _ inv
    refine ⟨endSt status, by simpa using index_nil_left (D m) r₂ _ status,
      Or.inr ⟨[], [], [], r₂, rfl, rfl, rfl, Or.inl rfl, by simpa using inv.endSt⟩,
      fun h => Or.inl (endSt_of_ne (by rcases h with h | h <;> rw [h] <;> simp)), endSt_ne status⟩
  | cons x xs ih =>
    intro r₂ p₁ p₂ status h₁ h₂ hp₁ hp₂ len inv
    cases r₂ with
    | nil =>
      refine ⟨endSt status, by simpa using index_nil_right (D m) (x :: xs) _ status,
        Or.inr ⟨[], x :: xs, [], [], rfl, rfl, rfl, Or.inr rfl, by simpa using inv.endSt⟩,
        fun h => Or.inl (endSt_of_ne (by rcases h with h | h <;> rw [h] <;> simp)), endSt_ne status⟩
    | cons y ys =>
      have hx : E x := h₁ x List.mem_cons_self
      have hy : E y := h₂ y List.mem_cons_self
      have h₁' : ∀ e ∈ xs, E e := fun e m => h₁ e (List.mem_cons_of_mem _ m)
      have h₂' : ∀ e ∈ ys, E e := fun e m => h₂ e (List.mem_cons_of_mem _ m)
      have hp₁' : ∀ e ∈ p₁ ++ [x], E e := fun e m => by
        rcases List.mem_append.mp m with m | m
        · exact hp₁ e m
        · simp at m; subst m; exact hx
      have hp₂' : ∀ e ∈ p₂ ++ [y], E e := fun e m => by
        rcases List.mem_append.mp m with m | m
        · exact hp₂ e m
        · simp at m; subst m; exact hy
      have len' : (p₁ ++ [x]).length = (p₂ ++ [y]).length := by simp [len]
      have lenS : ((p₁ ++ [x]).length : Int) = ((p₁.length + 1 : Nat) : Int) := by simp
      -- continuing the walk with a new status
      have cont : ∀ st, StatusInv den st (p₁ ++ [x]) (p₂ ++ [y]) → ∃ res,
          Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m) (Term.list xs) (Term.list ys)
            (.integer ((p₁.length + 1 : Nat) : Int)) st = .ok res ∧
          (res = Term.atom "none" ∨ ∃ c₁ s₁ c₂ s₂, x :: xs = c₁ ++ s₁ ∧ y :: ys = c₂ ++ s₂ ∧ c₁.length = c₂.length ∧
            (s₁ = [] ∨ s₂ = []) ∧ StatusInv den res (p₁ ++ c₁) (p₂ ++ c₂)) ∧
          (st = .atom "left_subtype_of_right" ∨ st = .atom "right_subtype_of_left" →
            res = st ∨ res = .atom "none") ∧ res ≠ .atom "all_equal" := by
        intro st inv'
        obtain ⟨res, run, out, keep, ne⟩ := ih ys (p₁ ++ [x]) (p₂ ++ [y]) st h₁' h₂' hp₁' hp₂' len' inv'
        rw [lenS] at run
        refine ⟨res, run, ?_, keep, ne⟩
        rcases out with e | ⟨c₁, s₁, c₂, s₂, e₁, e₂, lc, sc, inv''⟩
        · exact Or.inl e
        · refine Or.inr ⟨x :: c₁, s₁, y :: c₂, s₂, by simp [e₁], by simp [e₂], by simp [lc], sc, ?_⟩
          simpa using inv''
      by_cases same : compareExact (fuel y x) y x = .eq
      · have sd := same_of_exact ef hx hy same
        have inv' : StatusInv den status (p₁ ++ [x]) (p₂ ++ [y]) := by
          rcases inv with ⟨e, pr⟩ | ⟨j, d₁, d₂, a₁, b₁, a₂, b₂, e, rfl, rfl, lj, pa, pb, nd⟩ | ⟨e, pr⟩ | ⟨e, pr⟩
          · exact Or.inl ⟨e, pr.snoc sd⟩
          · exact Or.inr (Or.inl ⟨j, d₁, d₂, a₁, b₁ ++ [x], a₂, b₂ ++ [y], e, by simp, by simp, lj, pa, pb.snoc sd, nd⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨e, pr.snoc fun v h => (sd v).mp h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨e, pr.snoc fun v h => (sd v).mpr h⟩))
        obtain ⟨res, run, out, keep, ne⟩ := cont status inv'
        refine ⟨res, ?_, out, keep, ne⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
        simp [Erlang.erlang.«=:=/2», same]
        simpa [Term.list] using run
      rcases inv with ⟨rfl, pr⟩ | ⟨j, d₁, d₂, a₁, b₁, a₂, b₂, rfl, rfl, rfl, lj, pa, pb, nd⟩ | ⟨rfl, pr⟩ | ⟨rfl, pr⟩
      · obtain ⟨res, run, out, -, ne⟩ := cont (.tuple #[.atom "one_index_difference", .integer (p₁.length : Int), x, y])
          (Or.inr (Or.inl ⟨p₁.length, x, y, p₁, [], p₂, [], rfl, rfl, rfl, rfl, pr, trivial,
            fun h => same (Lynx.Term.compareExact_eq_symm h)⟩))
        refine ⟨res, ?_, out, fun h => by simp at h, ne⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
        simp [Erlang.erlang.«=:=/2», same]
        simpa [Term.list] using run
      · have hd₁ : E d₁ := hp₁ d₁ (by simp)
        have hd₂ : E d₂ := hp₂ d₂ (by simp)
        obtain ⟨s₁, r₁, k₁⟩ := sub_bool ef hm hd₁ hd₂
        obtain ⟨s₂, r₂, k₂⟩ := sub_bool ef hm hx hy
        obtain ⟨s₃, r₃, k₃⟩ := sub_bool ef hm hd₂ hd₁
        obtain ⟨s₄, r₄, k₄⟩ := sub_bool ef hm hy hx
        by_cases l : (s₁ && s₂) = Bool.true
        · simp only [Bool.and_eq_true] at l
          obtain ⟨rfl, rfl⟩ := l
          have pr : Pairs (SubD den) (a₁ ++ d₁ :: b₁ ++ [x]) (a₂ ++ d₂ :: b₂ ++ [y]) :=
            ((pa.mono fun _ _ h v => (h v).mp).append (show Pairs (SubD den) (d₁ :: b₁) (d₂ :: b₂) from
              ⟨k₁ rfl, pb.mono fun _ _ h v => (h v).mp⟩)).snoc (k₂ rfl)
          obtain ⟨res, run, out, -, ne⟩ := cont (.atom "left_subtype_of_right") (Or.inr (Or.inr (Or.inl ⟨rfl, pr⟩)))
          refine ⟨res, ?_, out, fun h => by simp at h, ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, r₂,
            Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
          simpa [Term.list] using run
        by_cases rr : (s₃ && s₄) = Bool.true
        · simp only [Bool.and_eq_true] at rr
          obtain ⟨rfl, rfl⟩ := rr
          have pr : Pairs (SubD den) (a₂ ++ d₂ :: b₂ ++ [y]) (a₁ ++ d₁ :: b₁ ++ [x]) :=
            ((pa.swap fun _ _ h v => (h v).mpr).append (show Pairs (SubD den) (d₂ :: b₂) (d₁ :: b₁) from
              ⟨k₃ rfl, pb.swap fun _ _ h v => (h v).mpr⟩)).snoc (k₄ rfl)
          obtain ⟨res, run, out, -, ne⟩ := cont (.atom "right_subtype_of_left") (Or.inr (Or.inr (Or.inr ⟨rfl, pr⟩)))
          refine ⟨res, ?_, out, fun h => by simp at h, ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          cases s₁ <;> cases s₂ <;> simp at l <;>
            simp [Erlang.erlang.«=:=/2», same, r₁, r₂,
              r₃, r₄, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] <;>
            simpa [Term.list] using run
        · refine ⟨.atom "none", ?_, Or.inl rfl, fun _ => Or.inr rfl, by simp⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          cases s₁ <;> cases s₂ <;> cases s₃ <;> cases s₄ <;> simp at l rr <;>
            simp [Erlang.erlang.«=:=/2», same, r₁, r₂,
              r₃, r₄, Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
      · obtain ⟨s₁, r₁, k₁⟩ := sub_bool ef hm hx hy
        cases s₁
        · refine ⟨.atom "none", ?_, Or.inl rfl, fun _ => Or.inr rfl, by simp⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
        · obtain ⟨res, run, out, keep, ne⟩ := cont (.atom "left_subtype_of_right")
            (Or.inr (Or.inr (Or.inl ⟨rfl, pr.snoc (k₁ rfl)⟩)))
          refine ⟨res, ?_, out, fun _ => keep (Or.inl rfl), ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
          simpa [Term.list] using run
      · obtain ⟨s₁, r₁, k₁⟩ := sub_bool ef hm hy hx
        cases s₁
        · refine ⟨.atom "none", ?_, Or.inl rfl, fun _ => Or.inr rfl, by simp⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
        · obtain ⟨res, run, out, keep, ne⟩ := cont (.atom "right_subtype_of_left")
            (Or.inr (Or.inr (Or.inr ⟨rfl, pr.snoc (k₁ rfl)⟩)))
          refine ⟨res, ?_, out, fun _ => keep (Or.inr rfl), ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
          simpa [Term.list] using run

theorem inT_sub {c : Bool} : ∀ {a b : List Term}, Pairs (SubD den) a b → ∀ {v : List V}, InT den c a v → InT den c b v
  | [], [], _, _, h => h
  | _ :: _, _ :: _, _, [], h => h.elim
  | _ :: _, _ :: _, p, _ :: _, h => ⟨p.1 _ h.1, inT_sub p.2 h.2⟩
  | [], _ :: _, p, _, _ => p.elim
  | _ :: _, [], p, _, _ => p.elim

theorem inT_same {c : Bool} {a b : List Term} (p : Pairs (SameD den) a b) {v : List V} :
    InT den c a v ↔ InT den c b v :=
  ⟨inT_sub (p.mono fun _ _ h v => (h v).mp), inT_sub (p.swap fun _ _ h v => (h v).mpr)⟩

theorem inT_sub_open {c : Bool} {a b s : List Term} (p : Pairs (SubD den) a b) {v : List V} (h : InT den c (a ++ s) v) :
    InT den Bool.false b v := by
  obtain ⟨v₁, v₂, rfl, h₁, -⟩ := (InT.append a).mp h
  exact InT.extend v₂ (inT_sub p h₁)

/-- What `opt_tuple_union_strategy/4` answers about two tuple literals. -/
def StratOk (den : Term → V → Prop) (t₁ : String) (l₁ : List Term) (t₂ : String) (l₂ : List Term) (res : Term) : Prop :=
  res ≠ .atom "all_equal" ∧
  (∀ (j : Int) d₁ d₂, res = .tuple #[.atom "one_index_difference", .integer j, d₁, d₂] → t₁ = t₂ ∧
    ∃ a₁ b₁ a₂ b₂, l₁ = a₁ ++ d₁ :: b₁ ∧ l₂ = a₂ ++ d₂ :: b₂ ∧ (a₁.length : Int) = j ∧ Pairs (SameD den) a₁ a₂ ∧
      Pairs (SameD den) b₁ b₂ ∧ compareExact (fuel d₁ d₂) d₁ d₂ ≠ .eq) ∧
  (res = .atom "left_subtype_of_right" → ∀ v, InT den (t₁ == "closed") l₁ v → InT den (t₂ == "closed") l₂ v) ∧
  (res = .atom "right_subtype_of_left" → ∀ v, InT den (t₂ == "closed") l₂ v → InT den (t₁ == "closed") l₁ v)

theorem stratOk_none (den : Term → V → Prop) (t₁ : String) (l₁ : List Term) (t₂ : String) (l₂ : List Term) :
    StratOk den t₁ l₁ t₂ l₂ (.atom "none") :=
  ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

/-- `opt_tuple_union_strategy/4` answers soundly about two tuple literals of element types. -/
theorem strategy_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e) :
    ∃ res, Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» (D m) (.atom t₁) (Term.list l₁) (.atom t₂)
      (Term.list l₂) = .ok res ∧ StratOk den t₁ l₁ t₂ l₂ res := by
  have nil₁ : ∀ e ∈ ([] : List Term), E e := by simp
  rw [strategy_start _ t₁ t₂ g₁ g₂]
  by_cases c₁ : t₁ = t₂ ∧ l₁.length = l₂.length
  · rw [ite_eq_left c₁]
    obtain ⟨res, run, out, -, ne⟩ := walk ef hm l₁ l₂ [] [] (.atom "all_equal") h₁ h₂ nil₁ nil₁ rfl
      (Or.inl ⟨rfl, trivial⟩)
    refine ⟨res, by simpa using run, ?_⟩
    rcases out with rfl | ⟨c₁', s₁, c₂', s₂, rfl, rfl, lc, sc, inv⟩
    · exact stratOk_none den _ _ _ _
    have e₁ := split_full lc sc (Nat.le_of_eq c₁.2)
    have e₂ := split_full lc.symm sc.symm (Nat.le_of_eq c₁.2.symm)
    subst e₁ e₂
    simp only [List.nil_append, List.append_nil] at inv ⊢
    obtain ⟨rfl, -⟩ := c₁
    rcases inv with ⟨rfl, pr⟩ | ⟨j, d₁, d₂, a₁, b₁, a₂, b₂, rfl, rfl, rfl, lj, pa, pb, nd⟩ | ⟨rfl, pr⟩ | ⟨rfl, pr⟩
    · exact absurd rfl ne
    · refine ⟨fun h => by simp at h, fun j' d₁' d₂' h => ?_, fun h => by simp at h, fun h => by simp at h⟩
      simp only [Term.tuple.injEq] at h
      have ej := congrArg (fun a : Array Term => a[1]?) h
      have ed₁ := congrArg (fun a : Array Term => a[2]?) h
      have ed₂ := congrArg (fun a : Array Term => a[3]?) h
      simp at ej ed₁ ed₂
      subst ed₁ ed₂
      exact ⟨rfl, a₁, b₁, a₂, b₂, rfl, rfl, by omega, pa, pb, nd⟩
    · exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun _ v hv => inT_sub pr hv,
        fun h => by simp at h⟩
    · exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun h => by simp at h,
        fun _ v hv => inT_sub pr hv⟩
  rw [ite_eq_right c₁]
  by_cases c₂ : t₁ = "open" ∧ l₁.length ≤ l₂.length
  · rw [ite_eq_left c₂]
    obtain ⟨res, run, out, keep, -⟩ := walk ef hm l₁ l₂ [] [] (.atom "right_subtype_of_left") h₁ h₂ nil₁ nil₁ rfl
      (Or.inr (Or.inr (Or.inr ⟨rfl, trivial⟩)))
    refine ⟨res, by simpa using run, ?_⟩
    rcases keep (Or.inr rfl) with rfl | rfl
    · rcases out with h | ⟨c₁', s₁, c₂', s₂, rfl, rfl, lc, sc, inv⟩
      · simp at h
      have e₁ := split_full lc sc c₂.2
      subst e₁
      simp only [List.nil_append] at inv
      rcases inv with ⟨h, -⟩ | ⟨_, _, _, _, _, _, _, h, -⟩ | ⟨h, -⟩ | ⟨-, pr⟩ <;> try simp at h
      obtain ⟨rfl, -⟩ := c₂
      exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun h => by simp at h,
        fun _ v hv => by simpa using inT_sub_open pr hv⟩
    · exact stratOk_none den _ _ _ _
  rw [ite_eq_right c₂]
  by_cases c₃ : t₂ = "open" ∧ l₂.length ≤ l₁.length
  · rw [ite_eq_left c₃]
    obtain ⟨res, run, out, keep, -⟩ := walk ef hm l₁ l₂ [] [] (.atom "left_subtype_of_right") h₁ h₂ nil₁ nil₁ rfl
      (Or.inr (Or.inr (Or.inl ⟨rfl, trivial⟩)))
    refine ⟨res, by simpa using run, ?_⟩
    rcases keep (Or.inl rfl) with rfl | rfl
    · rcases out with h | ⟨c₁', s₁, c₂', s₂, rfl, rfl, lc, sc, inv⟩
      · simp at h
      have e₂ := split_full lc.symm sc.symm c₃.2
      subst e₂
      simp only [List.nil_append] at inv
      rcases inv with ⟨h, -⟩ | ⟨_, _, _, _, _, _, _, h, -⟩ | ⟨-, pr⟩ | ⟨h, -⟩ <;> try simp at h
      obtain ⟨rfl, -⟩ := c₃
      exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun _ v hv => by simpa using inT_sub_open pr hv,
        fun h => by simp at h⟩
    · exact stratOk_none den _ _ _ _
  · rw [ite_eq_right c₃]
    exact ⟨_, rfl, stratOk_none den _ _ _ _⟩

theorem StatusInv.form {res : Term} {p q : List Term} (h : StatusInv den res p q) : StatusForm res := by
  rcases h with ⟨rfl, -⟩ | ⟨j, d₁, d₂, -, -, -, -, rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨j, d₁, d₂, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem strategy_form (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e)
    {res : Term} (run : Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» (D m) (.atom t₁) (Term.list l₁) (.atom t₂)
      (Term.list l₂) = .ok res) : StatusForm res := by
  have nil₁ : ∀ e ∈ ([] : List Term), E e := by simp
  have fromWalk : ∀ st, StatusInv den st [] [] → Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m)
      (Term.list l₁) (Term.list l₂) (.integer 0) st = .ok res → StatusForm res := by
    intro st inv w
    obtain ⟨res', run', out, -, -⟩ := walk ef hm l₁ l₂ [] [] st h₁ h₂ nil₁ nil₁ rfl inv
    have run'' : Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m) (Term.list l₁) (Term.list l₂)
        (.integer 0) st = .ok res' := by simpa using run'
    rw [w] at run''
    cases run''
    rcases out with rfl | ⟨_, _, _, _, -, -, -, -, inv'⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact inv'.form
  rw [strategy_start _ t₁ t₂ g₁ g₂] at run
  by_cases c₁ : t₁ = t₂ ∧ l₁.length = l₂.length
  · rw [ite_eq_left c₁] at run; exact fromWalk _ (Or.inl ⟨rfl, trivial⟩) run
  rw [ite_eq_right c₁] at run
  by_cases c₂ : t₁ = "open" ∧ l₁.length ≤ l₂.length
  · rw [ite_eq_left c₂] at run; exact fromWalk _ (Or.inr (Or.inr (Or.inr ⟨rfl, trivial⟩))) run
  rw [ite_eq_right c₂] at run
  by_cases c₃ : t₂ = "open" ∧ l₂.length ≤ l₁.length
  · rw [ite_eq_left c₃] at run; exact fromWalk _ (Or.inr (Or.inr (Or.inl ⟨rfl, trivial⟩))) run
  rw [ite_eq_right c₃] at run
  cases run
  exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem union_one_index {c : Bool} {a₁ b₁ a₂ b₂ : List Term} {d₁ d₂ u : Term} (pa : Pairs (SameD den) a₁ a₂)
    (pb : Pairs (SameD den) b₁ b₂) (su : ∀ v, den u v ↔ den d₁ v ∨ den d₂ v) (v : List V) :
    InT den c (a₁ ++ u :: b₁) v ↔ InT den c (a₁ ++ d₁ :: b₁) v ∨ InT den c (a₂ ++ d₂ :: b₂) v := by
  constructor
  · intro h
    obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid a₁ u b₁).mp h
    rcases (su y).mp hy with hy | hy
    · exact Or.inl ((InT.mid a₁ d₁ b₁).mpr ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩)
    · exact Or.inr ((InT.mid a₂ d₂ b₂).mpr ⟨v₁, y, v₂, rfl, (inT_same pa).mp h₁, hy, (inT_same pb).mp h₂⟩)
  · rintro (h | h)
    · exact h.replace fun y hy => (su y).mpr (Or.inl hy)
    · obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid a₂ d₂ b₂).mp h
      exact (InT.mid a₁ u b₁).mpr ⟨v₁, y, v₂, rfl, (inT_same pa).mpr h₁, (su y).mpr (Or.inr hy), (inT_same pb).mpr h₂⟩

end Elixir.STTDescrProofsTest.Nest
