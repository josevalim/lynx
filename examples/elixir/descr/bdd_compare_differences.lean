namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences guided by comparing leaves, exact for the valuations that agree with the comparisons. -/

/-- Leaves of literals `ok`, or the empty BDD. -/
def LeafOrBot (ok : Term → Prop) (t : Term) : Prop :=
  t = .atom "bdd_bot" ∨ ∃ (k : Int) (x y : Term), t = .tuple #[.integer k, x, y] ∧ ok t

theorem LeafOrBot.bdd {ok : Term → Prop} {t : Term} (h : LeafOrBot ok t) : Bdd ok t := by
  rcases h with rfl | ⟨k, x, y, rfl, okt⟩
  · exact Bdd.bot
  · exact Bdd.leaf_iff.mpr okt

/-- What a leaf comparison answers about two literals, for the valuations `Val`. -/
def CmpOk (Val : (Term → Bool) → Prop) (ok : Term → Prop) (a₁ a₂ type res : Term) : Prop :=
  (res = .atom "disjoint" ∧ ∀ ρ, Val ρ → (ρ a₁ && ρ a₂) = Bool.false) ∨
  (res = .atom "subtype" ∧ ∀ ρ, Val ρ → ρ a₁ = Bool.true → ρ a₂ = Bool.true) ∨
  (∃ ad at', res = .tuple #[.atom "one_key_difference", ad, at'] ∧ LeafOrBot ok ad ∧ LeafOrBot ok at' ∧
    (∀ ρ, Val ρ → eval ρ ad = (ρ a₁ && !ρ a₂)) ∧
    (type = .atom "intersection" → ∀ ρ, Val ρ → eval ρ at' = (ρ a₁ && ρ a₂)) ∧
    (type = .atom "union" → ∀ ρ, Val ρ → eval ρ at' = (ρ a₁ || ρ a₂)) ∧
    (type = .atom "none" → at' = .atom "bdd_bot")) ∨
  res = .atom "none"

/-- The types of results `bdd_difference/3` asks leaf comparisons for. -/
def TypeOk (type : Term) : Prop := type = .atom "none" ∨ type = .atom "intersection" ∨ type = .atom "union"

/-- What `bdd_difference/3` guarantees. -/
def Diff3 (Val : (Term → Bool) → Prop) (ok : Term → Prop) (d : Dispatcher) (cmp a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_difference/3» d a b cmp = .ok r ∧ Bdd ok r ∧
    ∀ ρ, Val ρ → eval ρ r = (eval ρ a && !eval ρ b)

theorem diff3_plain {Val : (Term → Bool) → Prop} (resp : ∀ ρ, Val ρ → Resp ρ) {ok : Term → Prop} {d : Dispatcher}
    {cmp a b : Term} (wa : Bdd ok a) (wb : Bdd ok b)
    (run : Elixir.Module.Types.Descr.«bdd_difference/3» d a b cmp = Elixir.Module.Types.Descr.«bdd_difference/2» a b) :
    Diff3 Val ok d cmp a b := by
  obtain ⟨r, hr, okr, semr⟩ := diff_ok wa wb
  exact ⟨r, by rw [run, hr], okr ok wa wb, fun ρ v => semr ρ (resp ρ v)⟩

theorem d3_top_left (d : Dispatcher) (b cmp : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/3» d (.atom "bdd_top") b cmp =
      Elixir.Module.Types.Descr.«bdd_difference/2» (.atom "bdd_top") b := by
  rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]

theorem d3_bot_left (d : Dispatcher) (b cmp : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/3» d (.atom "bdd_bot") b cmp =
      Elixir.Module.Types.Descr.«bdd_difference/2» (.atom "bdd_bot") b := by
  rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]

theorem d3_atom_right {ok : Term → Prop} (d : Dispatcher) {a : Term} (wa : Bdd ok a) (s : String) (cmp : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/3» d a (.atom s) cmp =
      Elixir.Module.Types.Descr.«bdd_difference/2» a (.atom s) := by
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d', rfl⟩ <;>
    rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]

variable {Val : (Term → Bool) → Prop} {ok : Term → Prop} {d : Dispatcher} {cmp : Term}

/-- Leaves minus leaves. -/
theorem diff3_leaves (resp : ∀ ρ, Val ρ → Resp ρ)
    (spec : ∀ a₁ a₂ type, TypeOk type → ok a₁ → ok a₂ →
      ∃ res, d.pure cmp #[a₁, a₂, type] = .ok res ∧ CmpOk Val ok a₁ a₂ type res)
    (k₁ : Int) (x₁ y₁ : Term) (k₂ : Int) (x₂ y₂ : Term) (h₁ : ok (.tuple #[.integer k₁, x₁, y₁]))
    (h₂ : ok (.tuple #[.integer k₂, x₂, y₂])) :
    Diff3 Val ok d cmp (.tuple #[.integer k₁, x₁, y₁]) (.tuple #[.integer k₂, x₂, y₂]) := by
  obtain ⟨res, run, cmpOk⟩ := spec _ _ (.atom "none") (Or.inl rfl) h₁ h₂
  have w₁ : Bdd ok (.tuple #[.integer k₁, x₁, y₁]) := Bdd.leaf_iff.mpr h₁
  have w₂ : Bdd ok (.tuple #[.integer k₂, x₂, y₂]) := Bdd.leaf_iff.mpr h₂
  rcases cmpOk with ⟨rfl, disj⟩ | ⟨rfl, sub⟩ | ⟨ad, at', rfl, had, -, sad, -, -, -⟩ | rfl
  · refine ⟨_, ?_, w₁, fun ρ v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]; rfl
    · have := disj ρ v
      simp only [eval_leaf] at this ⊢
      revert this; cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> simp
  · refine ⟨_, ?_, Bdd.bot, fun ρ v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]; rfl
    · have := sub ρ v
      simp only [eval_leaf] at this ⊢
      revert this; cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> simp
  · refine ⟨ad, ?_, had.bdd, fun ρ v => by simp only [eval_leaf]; exact sad ρ v⟩
    rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]; rfl
  · refine diff3_plain resp w₁ w₂ ?_
    rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]

theorem eq_bot_atom (x : Term) [Decidable (x = .atom "bdd_bot")] :
    Erlang.erlang.«==/2» x (.atom "bdd_bot") = .ok (.atom (if x = .atom "bdd_bot" then "true" else "false")) := by
  by_cases h : x = .atom "bdd_bot"
  · subst h; simp [Erlang.erlang.«==/2»]
  · simp [Erlang.erlang.«==/2», h]

/-- BDDs minus leaves. -/
theorem diff3_left (resp : ∀ ρ, Val ρ → Resp ρ)
    (spec : ∀ a₁ a₂ type, TypeOk type → ok a₁ → ok a₂ →
      ∃ res, d.pure cmp #[a₁, a₂, type] = .ok res ∧ CmpOk Val ok a₁ a₂ type res) :
    ∀ ok₁ b₁, Bdd ok₁ b₁ → (∀ t, ok₁ t → ok t) → ∀ (k : Int) x y, ok (.tuple #[.integer k, x, y]) →
      Diff3 Val ok d cmp b₁ (.tuple #[.integer k, x, y]) := by
  refine Bdd.induction (P := fun ok₁ b₁ => (∀ t, ok₁ t → ok t) → ∀ (k : Int) x y, ok (.tuple #[.integer k, x, y]) →
    Diff3 Val ok d cmp b₁ (.tuple #[.integer k, x, y])) ?_ ?_ ?_ ?_
  · intro ok₁ _ k x y h; exact diff3_plain resp Bdd.top (Bdd.leaf_iff.mpr h) (d3_top_left _ _ _)
  · intro ok₁ _ k x y h; exact diff3_plain resp Bdd.bot (Bdd.leaf_iff.mpr h) (d3_bot_left _ _ _)
  · intro ok₁ k₁ x₁ y₁ h₁ sub k x y h; exact diff3_leaves resp spec k₁ x₁ y₁ k x y (sub _ h₁) h
  · intro ok₁ hh a₁ c₁ u₁ d₁ isLeaf oka hc hu hd ic iu id sub k x y h₂
    have sub' : ∀ t, Above ok₁ a₁ t → ok t := fun t ht => sub t ht.1
    have lift : ∀ t, Above ok₁ a₁ t → Above ok a₁ t := fun t ht => ⟨sub t ht.1, ht.2⟩
    have w₁ : Bdd ok (.tuple #[.integer hh, a₁, c₁, u₁, d₁]) :=
      Bdd.node_iff.mpr ⟨isLeaf, sub _ oka, hc.mono lift, hu.mono lift, hd.mono lift⟩
    have w₂ : Bdd ok (.tuple #[.integer k, x, y]) := Bdd.leaf_iff.mpr h₂
    have wc : Bdd ok c₁ := hc.mono fun t ht => sub t ht.1
    have wu : Bdd ok u₁ := hu.mono fun t ht => sub t ht.1
    have wd : Bdd ok d₁ := hd.mono fun t ht => sub t ht.1
    obtain ⟨k₁, x₁, y₁, rfl⟩ := isLeaf
    classical
    let type : Term := .atom (if d₁ = .atom "bdd_bot" then "none" else "union")
    obtain ⟨res, run, cmpOk⟩ := spec _ _ type (by simp only [type]; split <;> simp [TypeOk]) (sub _ oka) h₂
    obtain ⟨ru, hru, okru, semru⟩ := iu sub' k x y h₂
    rcases cmpOk with ⟨rfl, -⟩ | ⟨rfl, sb⟩ | ⟨ad, au, rfl, had, hau, sad, -, sau, snone⟩ | rfl
    · obtain ⟨hn, runn⟩ := node_new (.tuple #[.integer k₁, x₁, y₁]) c₁ (.atom "bdd_bot") d₁ ⟨k₁, x₁, y₁, rfl⟩ hc
        (Bdd.bot (ok := ok₁)) hd
      have wn : Bdd ok (.tuple #[.integer hn, .tuple #[.integer k₁, x₁, y₁], c₁, .atom "bdd_bot", d₁]) :=
        Bdd.node_iff.mpr ⟨⟨k₁, x₁, y₁, rfl⟩, sub _ oka, hc.mono lift, Bdd.bot, hd.mono lift⟩
      obtain ⟨r₂, hr₂, okr₂, semr₂⟩ := diff_ok wn w₂
      obtain ⟨r, hr, okr, semr⟩ := union_ok (okru) (okr₂ ok wn w₂)
      refine ⟨r, ?_, okr ok okru (okr₂ ok wn w₂), fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_bot_atom]
        by_cases e : d₁ = .atom "bdd_bot"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hru, runn, hr₂, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hru, runn, hr₂, hr]
      · rw [semr ρ (resp ρ v), semru ρ v, semr₂ ρ (resp ρ v)]
        simp only [eval]
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
          cases eval ρ u₁ <;> cases eval ρ d₁ <;> rfl
    · obtain ⟨rd, hrd, okrd, semrd⟩ := id sub' k x y h₂
      obtain ⟨r, hr, okr, semr⟩ := union_ok okru okrd
      refine ⟨r, ?_, okr ok okru okrd, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_bot_atom]
        by_cases e : d₁ = .atom "bdd_bot"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hru, hrd, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hru, hrd, hr]
      · rw [semr ρ (resp ρ v), semru ρ v, semrd ρ v]
        have := sb ρ v
        simp only [eval_node, eval_leaf]
        revert this
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
          cases eval ρ u₁ <;> cases eval ρ d₁ <;> simp
    · obtain ⟨ri, hri, okri, semri⟩ := inter_ok had.bdd wc
      obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := union_ok (okri ok had.bdd wc) okru
      obtain ⟨rd, hrd, okrd, semrd⟩ : Diff3 Val ok d cmp d₁ au := by
        by_cases e : d₁ = .atom "bdd_bot"
        · subst e; exact diff3_plain resp Bdd.bot hau.bdd (d3_bot_left _ _ _)
        · rcases hau with rfl | ⟨k', x', y', rfl, okau⟩
          · exact diff3_plain resp wd Bdd.bot (d3_atom_right _ wd _ _)
          · exact id sub' k' x' y' okau
      obtain ⟨r, hr, okr, semr⟩ := union_ok (okr₁ ok (okri ok had.bdd wc) okru) okrd
      refine ⟨r, ?_, okr ok (okr₁ ok (okri ok had.bdd wc) okru) okrd, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_bot_atom]
        by_cases e : d₁ = .atom "bdd_bot"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hri, hru, hr₁, hrd, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hri, hru, hr₁, hrd, hr]
      · rw [semr ρ (resp ρ v), semr₁ ρ (resp ρ v), semri ρ (resp ρ v), semru ρ v, semrd ρ v, sad ρ v]
        simp only [eval_node, eval_leaf]
        by_cases e : d₁ = .atom "bdd_bot"
        · have := snone (by simp [type, e])
          subst this e
          try simp only [eval]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
            cases eval ρ u₁ <;> rfl
        · rw [sau (by simp [type, e]) ρ v]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
            cases eval ρ u₁ <;> cases eval ρ d₁ <;> rfl
    · refine diff3_plain resp w₁ w₂ ?_
      rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
      simp only [eq_bot_atom]
      by_cases e : d₁ = .atom "bdd_bot"
      · simp only [ite_eq_left e, type] at run ⊢; simp [run]
      · simp only [ite_eq_right e, type] at run ⊢; simp [run]

theorem eq_top_atom (x : Term) [Decidable (x = .atom "bdd_top")] :
    Erlang.erlang.«==/2» x (.atom "bdd_top") = .ok (.atom (if x = .atom "bdd_top" then "true" else "false")) := by
  by_cases h : x = .atom "bdd_top"
  · subst h; simp [Erlang.erlang.«==/2»]
  · simp [Erlang.erlang.«==/2», h]

/-- `bdd_difference/3` subtracts BDDs exactly, for the valuations its leaf comparisons are right about. -/
theorem diff3_ok (resp : ∀ ρ, Val ρ → Resp ρ)
    (spec : ∀ a₁ a₂ type, TypeOk type → ok a₁ → ok a₂ →
      ∃ res, d.pure cmp #[a₁, a₂, type] = .ok res ∧ CmpOk Val ok a₁ a₂ type res) :
    ∀ ok₂ b₂, Bdd ok₂ b₂ → (∀ t, ok₂ t → ok t) → ∀ b₁, Bdd ok b₁ → Diff3 Val ok d cmp b₁ b₂ := by
  refine Bdd.induction (P := fun ok₂ b₂ => (∀ t, ok₂ t → ok t) → ∀ b₁, Bdd ok b₁ → Diff3 Val ok d cmp b₁ b₂)
    ?_ ?_ ?_ ?_
  · intro ok₂ _ b₁ w₁; exact diff3_plain resp w₁ Bdd.top (d3_atom_right _ w₁ _ _)
  · intro ok₂ _ b₁ w₁; exact diff3_plain resp w₁ Bdd.bot (d3_atom_right _ w₁ _ _)
  · intro ok₂ k x y h sub b₁ w₁; exact diff3_left resp spec ok b₁ w₁ (fun _ h => h) k x y (sub _ h)
  · intro ok₂ hh a₂ c₂ u₂ d₂ isLeaf oka hc hu hd ic iu id sub b₁ w₁
    have sub' : ∀ t, Above ok₂ a₂ t → ok t := fun t ht => sub t ht.1
    have lift : ∀ t, Above ok₂ a₂ t → Above ok a₂ t := fun t ht => ⟨sub t ht.1, ht.2⟩
    have w₂ : Bdd ok (.tuple #[.integer hh, a₂, c₂, u₂, d₂]) :=
      Bdd.node_iff.mpr ⟨isLeaf, sub _ oka, hc.mono lift, hu.mono lift, hd.mono lift⟩
    obtain ⟨k₂, x₂, y₂, rfl⟩ := isLeaf
    rcases w₁.shape with rfl | rfl | ⟨k₁, x₁, y₁, rfl⟩ | ⟨h₁, l₁, c₁, u₁, d₁, rfl⟩
    · exact diff3_plain resp w₁ w₂ (d3_top_left _ _ _)
    · exact diff3_plain resp w₁ w₂ (d3_bot_left _ _ _)
    rotate_left
    · exact diff3_plain resp w₁ w₂ (by rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def])
    have h₁ : ok (.tuple #[.integer k₁, x₁, y₁]) := Bdd.leaf_iff.mp w₁
    classical
    let type : Term := .atom (if c₂ = .atom "bdd_top" then "none" else "intersection")
    obtain ⟨res, run, cmpOk⟩ := spec _ _ type (by simp only [type]; split <;> simp [TypeOk]) h₁ (sub _ oka)
    rcases cmpOk with ⟨rfl, dj⟩ | ⟨rfl, sb⟩ | ⟨ad, ai, rfl, had, hai, sad, sai, -, snone⟩ | rfl
    · obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := id sub' _ w₁
      obtain ⟨r, hr, okr, semr⟩ := iu sub' _ okr₁
      refine ⟨r, ?_, okr, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_top_atom]
        by_cases e : c₂ = .atom "bdd_top"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hr₁, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hr₁, hr]
      · rw [semr ρ v, semr₁ ρ v]
        have := dj ρ v
        simp only [eval_node, eval_leaf] at this ⊢
        revert this
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> cases eval ρ c₂ <;>
          cases eval ρ u₂ <;> cases eval ρ d₂ <;> simp
    · obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := ic sub' _ w₁
      obtain ⟨r, hr, okr, semr⟩ := iu sub' _ okr₁
      refine ⟨r, ?_, okr, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_top_atom]
        by_cases e : c₂ = .atom "bdd_top"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hr₁, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hr₁, hr]
      · rw [semr ρ v, semr₁ ρ v]
        have := sb ρ v
        simp only [eval_node, eval_leaf] at this ⊢
        revert this
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> cases eval ρ c₂ <;>
          cases eval ρ u₂ <;> cases eval ρ d₂ <;> simp
    · obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := id sub' _ had.bdd
      obtain ⟨r₂, hr₂, okr₂, semr₂⟩ := iu sub' _ okr₁
      obtain ⟨r₃, hr₃, okr₃, semr₃⟩ := ic sub' _ hai.bdd
      obtain ⟨r₄, hr₄, okr₄, semr₄⟩ := iu sub' _ okr₃
      obtain ⟨r, hr, okr, semr⟩ := union_ok okr₂ okr₄
      refine ⟨r, ?_, okr ok okr₂ okr₄, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_top_atom]
        by_cases e : c₂ = .atom "bdd_top"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hr₁, hr₂, hr₃, hr₄, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hr₁, hr₂, hr₃, hr₄, hr]
      · rw [semr ρ (resp ρ v), semr₂ ρ v, semr₁ ρ v, semr₄ ρ v, semr₃ ρ v, sad ρ v]
        simp only [eval_node, eval_leaf]
        by_cases e : c₂ = .atom "bdd_top"
        · have := snone (by simp [type, e])
          subst this e
          simp only [eval]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;>
            cases eval ρ u₂ <;> cases eval ρ d₂ <;> rfl
        · rw [sai (by simp [type, e]) ρ v]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> cases eval ρ c₂ <;>
            cases eval ρ u₂ <;> cases eval ρ d₂ <;> rfl
    · refine diff3_plain resp w₁ w₂ ?_
      rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
      simp only [eq_top_atom]
      by_cases e : c₂ = .atom "bdd_top"
      · simp only [ite_eq_left e, type] at run ⊢; simp [run]
      · simp only [ite_eq_right e, type] at run ⊢; simp [run]

end Elixir.STTDescrProofsTest
