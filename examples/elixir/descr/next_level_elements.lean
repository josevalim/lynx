namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The element types of the next level: the top type and types over the structural kinds of element types. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem EF.funB (ef : EF nd E V den tl K) (N : Nat) : ElemFun (EB E N) K where
  static := fun ha => ef.static ha.1
  union := fun ha hb => let ⟨c, hc, run, _, h⟩ := ef.union ha.1 hb.1; ⟨c, ⟨hc, h N ha.2 hb.2⟩, run⟩
  sub := fun ha hb => let ⟨s, run, _⟩ := ef.sub ha.1 hb.1; ⟨s, run⟩
  disj := fun ha hb => let ⟨s, run, _⟩ := ef.disj ha.1 hb.1; ⟨s, run⟩

theorem EF.tailB (ef : EF nd E V den tl K) (N : Nat) : TailOk (EB E N) := fun _ he =>
  let ⟨e', run, he', _, hl⟩ := ef.tail he.1
  ⟨e', run, he', by have := he.2; omega⟩

/-- Types over function fields `Fn` and fields `TF`, `LF`, and `MF`. -/
def DEG (Fn TF LF MF : Term → Prop) (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ DescrC Fn TF LF MF X

/-- Element types of the next level. -/
abbrev DE (E : Term → Prop) : Term → Prop := DEG (FunA E) (TField E) (LF E) (MField E)

/-- Points of types: a field name and a point valid there. -/
abbrev PtG (TV LV MV : (Term → Bool) → Prop) (FV : Term → (Term → Bool) → Prop) : Type :=
  {q : String × Point // q.1 ∈ names ∧ PtOkC TV LV MV FV q.1 q.2}

/-- Points of the next level. -/
abbrev PtOkD (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (FV : Term → (Term → Bool) → Prop)
    (name : String) (p : Point) : Prop :=
  PtOkC (ValT E den) (ValLN E den tl) (ValMN E den) FV name p

abbrev PtD (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (FV : Term → (Term → Bool) → Prop) : Type :=
  PtG (ValT E den) (ValLN E den tl) (ValMN E den) FV

section
variable {C : Nat → Term → Prop} {TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

def denD (a : Term) (q : PtG TV LV MV FV) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ dn q.1.1 (mapLookup X (.atom q.1.1)) q.1.2 = Bool.true

def tlD (q : PtG TV LV MV FV) : Prop := q.1.1 = "list"

theorem denD_term (q : PtG TV LV MV FV) : denD (.atom "term") q := Or.inl rfl

theorem denD_map {X : List (Term × Term)} (q : PtG TV LV MV FV) :
    denD (.map X) q ↔ dn q.1.1 (mapLookup X (.atom q.1.1)) q.1.2 = Bool.true := by
  simp [denD]

end

theorem de_nest (ef : EF nd E V den tl K) {a : Term} (ha : DE E a) {N : Nat} (h : lh a < N) : NestC (EB E N) a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨X, rfl, descr_nest ef sX h⟩

/-- The plain operations on element types of the next level, below a height, at every call depth. -/
theorem nest_ops (ef : EF nd E V den tl K) (hnone : E (.map [])) {N : Nat} (hN : 0 < N) :
    ElemOk (NestC (EB E N)) (K + 8) ∧ ElemDiff (NestC (EB E N)) (K + 3) ∧ ElemFun (NestC (EB E N)) (K + 14) := by
  have none : EB E N (.map []) := ⟨hnone, by rw [lh_nil_map]; exact hN⟩
  have term : EB E N (.atom "term") := ⟨ef.term, by simp [lh]; exact hN⟩
  exact ⟨nestOk (ef.ops N hN) (ef.dops N) (ef.funB N) none (ef.tailB N), nestDiff term K,
    nestFun (ef.ops N hN) (ef.dops N) (ef.funB N) none (ef.tailB N)⟩

theorem lh_term_zero : lh (.atom "term") = 0 := by simp [lh]

theorem fcOf (K : Nat) : FunC (K + 2) FunTop FVT (fun _ => True) True :=
  funTopC (by omega) ⟨.nil, fun _ => Bool.true, resp_const _, trivial⟩

/-- What the step to the next level needs: kinds of fields, function fields `Fn` whose points `FV` allows, holding
the top function type as their only fields of height zero, and the plain operations on a class `C N` of types
holding the types over those fields below each height `N`. -/
structure StepOk (nd : Term) (C : Nat → Term → Prop) (K : Nat) (Fn TF LF MF : Term → Prop)
    (TV LV MV : (Term → Bool) → Prop) (FV : Term → (Term → Bool) → Prop) : Prop where
  ks : Kinds (K + 2) TF LF MF TV LV MV
  fc : FunC (K + 2) Fn FV (fun _ => True) True
  ftop : Fn funTopT
  fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT
  fvw : ∃ a ρ, Resp ρ ∧ FV a ρ
  nest : ∀ {a N}, DEG Fn TF LF MF a → lh a < N → C N a
  ops : ∀ {N}, 0 < N → ElemOk (C N) (K + 8) ∧ ElemDiff (C N) (K + 3) ∧ ElemFun (C N) (K + 14)
  tz : ∀ {x}, TF x → lh x = 0 → ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]
  lz : ∀ {x}, LF x → lh x = 0 → x = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  mz : ∀ {x}, MF x → lh x = 0 → ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]
  treal : ∀ (c : Bool) {x}, TF x → OField (PureLit nd) x → ∃ ρ, TV ρ ∧ denO x ρ = denO x (fun _ => c)

theorem tz_of {x : Term} (fx : TField E x) (z : lh x = 0) : ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil] := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, rfl⟩
  · have := tbdd_pos wx; omega

theorem mz_of {x : Term} (fx : MField E x) (z : lh x = 0) : ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil] := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, rfl⟩
  · have := mbdd_pos wx; omega

theorem lz_of (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (z : lh x = 0) :
    x = .tuple #[.integer 46675407, .atom "term", .atom "term"] := by
  rcases wx.shape with rfl | rfl | ⟨k, a, c, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · simp [lh] at z
  · simp [lh] at z
  · obtain ⟨k', a', c', e, ha, hc⟩ := Bdd.leaf_iff.mp wx
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    by_cases nt : k = 46675407 ∧ a = .atom "term" ∧ c = .atom "term"
    · obtain ⟨rfl, rfl, rfl⟩ := nt; rfl
    · rw [nl_lh_leaf (ef.shape hc) nt] at z; omega
  · obtain ⟨-, okl, -⟩ := Bdd.node_iff.mp wx
    obtain ⟨k', a', c', rfl, ha', -⟩ := okl
    rw [nl_lh_node (ef.shape ha')] at z
    omega

/-- Tuple valuations of element types hold or leave out the expansion literal of the node, as wanted. -/
theorem treal_of (ef : EF nd E V den tl K) (c : Bool) {x : Term} (fx : TField E x) (px : OField (PureLit nd) x) :
    ∃ ρ, ValT E den ρ ∧ denO x ρ = denO x (fun _ => c) := by
  rcases pure_cases px with ⟨k, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c', u, d, he, rfl⟩
  · exact ⟨_, ⟨[], rfl⟩, by simp [denO_top]⟩
  · exact ⟨_, ⟨[], rfl⟩, rfl⟩
  · exact ⟨_, ⟨[], rfl⟩, rfl⟩
  · have hl : TLit E (litN e (keyOf nd)) := by
      rcases fx with ⟨k, h⟩ | wx
      · simp [litN, Term.list] at h
      · exact Bdd.leaf_iff.mp wx
    obtain ⟨⟨v₁, h₁⟩, ⟨v₀, h₀⟩⟩ := ef.litN_vals (litN_el hl) he (keyOf nd)
    cases c
    · exact ⟨_, ⟨v₀, rfl⟩, by simp [denO, isOpenTop, litN, Term.list] at h₀ ⊢; exact h₀⟩
    · exact ⟨_, ⟨v₁, rfl⟩, by simp [denO, isOpenTop, litN, Term.list] at h₁ ⊢; exact h₁⟩
  · have hl : TLit E (litN e (keyOf nd)) := by
      rcases fx with ⟨k, h⟩ | wx
      · simp at h
      · exact (Bdd.node_iff.mp wx).2.1
    obtain ⟨⟨v₁, h₁⟩, ⟨v₀, h₀⟩⟩ := ef.litN_vals (litN_el hl) he (keyOf nd)
    cases c
    · refine ⟨_, ⟨v₀, rfl⟩, ?_⟩
      simp only [litN, Term.list] at h₀
      cases c' <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list, h₀]
    · refine ⟨_, ⟨v₁, rfl⟩, ?_⟩
      simp only [litN, Term.list] at h₁
      cases c' <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list, h₁]

end

section
variable {nd : Term} {C : Nat → Term → Prop} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

/-- Unions of element types of the next level. -/
theorem de_union (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ c, DEG Fn TF LF MF c ∧ (∀ m, K + 14 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
      (∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∨ denD b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, fun m _ => union_term_l _ _, fun v => by simp [denD_term],
      fun N h _ => h⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, fun m _ => union_term_r _ _, fun v => by simp [denD_term],
      fun N _ h => h⟩
  have hN : 0 < max (lh (.map A)) (lh (.map B)) + 1 := by omega
  obtain ⟨c, -, run⟩ := (st.ops hN).2.2.union (st.nest (Or.inr ⟨A, rfl, sA⟩) (by omega))
    (st.nest (Or.inr ⟨B, rfl, sB⟩) (by omega))
  obtain ⟨U, run', sU, sem, le'⟩ := descr_union st.ks st.fc (m := K + 14) (by omega) sA sB
  have le := le' trivial
  have e := (run (K + 15) (by omega)).symm.trans run'
  simp only [Except.ok.injEq] at e
  subst e
  refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_, fun N h₁ h₂ => by omega⟩
  simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]

/-- Intersections of element types of the next level. -/
theorem de_inter (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ c, DEG Fn TF LF MF c ∧ (∀ m, K + 8 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
      (∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ denD b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, fun m _ => inter_term_left _ _, fun v => by simp [denD_term], fun N _ h => h⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, fun m _ => inter_term_right _ _, fun v => by simp [denD_term],
      fun N h _ => h⟩
  have hN : 0 < max (lh (.map A)) (lh (.map B)) + 1 := by omega
  obtain ⟨c, -, run⟩ := (st.ops hN).1.inter (st.nest (Or.inr ⟨A, rfl, sA⟩) (by omega))
    (st.nest (Or.inr ⟨B, rfl, sB⟩) (by omega))
  obtain ⟨U, run', sU, sem, le'⟩ := descr_inter st.ks st.fc (m := K + 8) (by omega) sA sB
  have le := le' trivial
  have e := (run (K + 9) (by omega)).symm.trans run'
  simp only [Except.ok.injEq] at e
  subst e
  refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_, fun N h₁ h₂ => by omega⟩
  simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]

theorem descrC_nil : DescrC Fn TF LF MF [] :=
  ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩

theorem lookup_out {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {name : String}
    (h : name ∉ names) : mapLookup X (.atom name) = none := by
  cases hx : mapLookup X (.atom name) with
  | none => rfl
  | some x =>
    obtain ⟨name', m, e⟩ := sX.keys _ (by rw [hx]; rfl)
    simp only [Term.atom.injEq] at e
    subst e; exact absurd m h

def ptWit : PtG TV LV MV FV := ⟨("atom", (0, .nil, fun _ => Bool.true)), by simp [names],
  ⟨resp_const _, by simp, by simp, by simp, by simp⟩⟩

theorem diff_none_right (d : Dispatcher) {a : Term} (ha : DEG Fn TF LF MF a) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map []) = .ok a := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]

/-- Differences of element types of the next level. -/
theorem de_diff (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ c, DEG Fn TF LF MF c ∧ (∀ m, K + 6 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
      (∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ ¬denD b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · refine ⟨_, Or.inr ⟨[], rfl, descrC_nil⟩, fun m _ => diff_term_right _ _, fun v => ?_,
      fun N _ _ => by rw [lh_nil_map]; omega⟩
    simp [denD_map, mapLookup, dn_none, denD_term]
  by_cases nB : B = []
  · subst nB
    exact ⟨a, ha, fun m _ => diff_none_right _ ha, fun v => by simp [denD_map, mapLookup, dn_none],
      fun N h _ => h⟩
  have hN : 0 < max (lh a) (lh (.map B)) + 1 := by omega
  obtain ⟨c, -, run⟩ := (st.ops hN).2.1.diff (st.nest ha (by omega))
    (st.nest (Or.inr ⟨B, rfl, sB⟩) (by omega))
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, lT, all⟩ := termC (FV := FV) st.ks st.ftop
    obtain ⟨U, run', sU, sem, le'⟩ := descr_diff st.ks st.fc (m := K + 4) (by omega) sT sB
    have le := le' trivial
    have e := (run (K + 6) (by omega)).symm.trans
      ((diff_term_left _ term sT.static sB.static nB).trans run')
    simp only [Except.ok.injEq] at e
    subst e
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, fun m hm => run m (by omega), fun v => ?_, fun N h₁ h₂ => by omega⟩
    simp only [denD_map, sem _ _ v.2.2, all _ v.2.1 _ v.2.2, denD_term, true_and, Bool.true_and,
      Bool.not_eq_true']
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run', sU, sem, le'⟩ := descr_diff st.ks st.fc (m := K + 4) (by omega) sA sB
    have le := le' trivial
    have e := (run (K + 6) (by omega)).symm.trans run'
    simp only [Except.ok.injEq] at e
    subst e
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, fun m hm => run m (by omega), fun v => ?_, fun N h₁ h₂ => by omega⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- Emptiness of element types of the next level, exact under safe seen sets. -/
theorem de_empty (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a : Term} (S : List (Term × Term)) (ha : DEG Fn TF LF MF a) :
    ∃ b : Bool, (∀ m, K + 8 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh a < N → SafeN N S → (b = Bool.true ↔ ∀ v : PtG TV LV MV FV, ¬denD a v) := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · refine ⟨Bool.false, fun m _ => by simpa [boolAtom] using empty_term _ _, fun N _ _ => ?_⟩
    refine ⟨fun h => absurd h (by simp), fun h => absurd (denD_term ptWit) (h ptWit)⟩
  have hN : 0 < lh (.map X) + 1 := by omega
  obtain ⟨b, run⟩ := (st.ops hN).1.empty (st.nest (Or.inr ⟨X, rfl, sX⟩) (by omega)) S
  obtain ⟨b', run', ex⟩ := descr_empty st.ks st.fc trivial (m := K + 8) (by omega) sX S trivial
  have e := (run (K + 8) (by omega)).symm.trans run'
  have : b = b' := by cases b <;> cases b' <;> simp_all [boolAtom]
  subst this
  refine ⟨b, run, fun N hl hS => ?_⟩
  obtain ⟨comp, sound⟩ := ex N hl hS
  constructor
  · intro bt v hv
    have := sound bt v.1.1 v.1.2 v.2.2
    rw [denD_map, this] at hv
    cases hv
  · intro none
    refine comp fun name p ok => ?_
    by_cases m : name ∈ names
    · have := none ⟨(name, p), m, ok⟩
      simpa [denD] using this
    · rw [lookup_out sX m, dn_none]

theorem empty_map_seen (d : Dispatcher) (A : List (Term × Term)) :
    Elixir.Module.Types.Descr.«empty?/1» d (.map A) = Elixir.Module.Types.Descr.«empty_seen?/2» d (.map A) (.map []) := by
  unfold Elixir.Module.Types.Descr.«empty?/1»; rfl

theorem bool_run {r : Except Exception Term} {s b : Bool} (h₁ : r = .ok (boolAtom s)) (h₂ : r = .ok (boolAtom b)) :
    s = b := by
  have := h₁.symm.trans h₂
  cases s <;> cases b <;> simp_all [boolAtom]

/-- Optimized unions of element types of the next level. -/
theorem de_opt_union (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term)) {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (hm : K + 4 ≤ m) : ∃ c, DEG Fn TF LF MF c ∧
      Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_left _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_union st.ks st.fc (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

/-- Optimized intersections of element types of the next level. -/
theorem de_opt_inter (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term)) {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (hm : K + 4 ≤ m) : ∃ c, DEG Fn TF LF MF c ∧
      Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, opt_inter_term_l _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, opt_inter_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_inter st.ks st.fc (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

/-- Optimized differences of element types of the next level. -/
theorem de_opt_diff (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term)) {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (hm : K + 6 ≤ m) : ∃ c, DEG Fn TF LF MF c ∧
      Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · refine ⟨_, Or.inr ⟨[], rfl, descrC_nil⟩, difference_term_term _ _ _, fun v => ?_⟩
    simp [denD_map, mapLookup, dn_none, denD_term]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · by_cases nB : B = []
    · subst nB
      exact ⟨_, Or.inl rfl, difference_term_none _ _, fun v => by simp [denD_map, mapLookup, dn_none, denD_term]⟩
    obtain ⟨T, term, sT, -, -, all⟩ := termC (FV := FV) st.ks st.ftop
    obtain ⟨U, run, sU, sem⟩ := descr_opt_diff st.ks st.fc (m := n) (by omega) sT sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, (opt_diff_term_left _ _ term sT.static sB.static nB).trans run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2, all _ v.2.1 _ v.2.2, denD_term, true_and, Bool.true_and]
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run, sU, sem⟩ := descr_opt_diff st.ks st.fc (m := n) (by omega) sA sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- Subtyping of element types of the next level: a uniform answer, sound. -/
theorem de_sub (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ s : Bool, (∀ m, K + 14 ≤ m → Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v : PtG TV LV MV FV, denD a v → denD b v) := by
  have hN : 0 < max (lh a) (lh b) + 1 := by omega
  obtain ⟨s, run⟩ := (st.ops hN).2.2.sub (st.nest ha (by omega)) (st.nest hb (by omega))
  refine ⟨s, run, fun st v hv => ?_⟩
  subst st
  have h : Elixir.Module.Types.Descr.«subtype?/2» (D (K + 14)) a b = .ok (boolAtom Bool.true) := run (K + 14) (by omega)
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact denD_term v
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, -, all⟩ := termC (FV := FV) st.ks st.ftop
    rw [subtype_term_l term] at h
    have := descr_sub_sound st.ks st.fc trivial trivial (by omega) sT sB h v.1.1 v.1.2 v.2.2
      (all _ v.2.1 _ v.2.2)
    exact (denD_map v).mpr this
  · exact (denD_map v).mpr (descr_sub_sound st.ks st.fc trivial trivial (by omega) sA sB h v.1.1 v.1.2 v.2.2
      ((denD_map v).mp hv))

theorem descr_incl {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A)
    (h : ∀ v : PtG TV LV MV FV, denD (.map A) v → denD (.map B) v) :
    ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true := by
  intro name p ok hx
  by_cases mn : name ∈ names
  · exact (denD_map ⟨(name, p), mn, ok⟩).mp (h _ ((denD_map _).mpr hx))
  · cases ha : mapLookup A (.atom name) with
    | none => rw [ha, dn_none] at hx; cases hx
    | some x =>
      obtain ⟨name', m', e⟩ := sA.keys _ (by rw [ha]; rfl)
      simp only [Term.atom.injEq] at e
      subst e; exact absurd m' mn

/-- Subtyping of element types of the next level is complete. -/
theorem de_subc (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (incl : ∀ v : PtG TV LV MV FV, denD a v → denD b v) {m : Nat} (hm : K + 14 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨T, term, sT, -, -, all⟩ := termC (FV := FV) st.ks st.ftop
  have toT : ∀ v : PtG TV LV MV FV, denD (.map T) v := fun v => (denD_map v).mpr (all _ v.2.1 _ v.2.2)
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [subtype_term_r term]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · rw [subtype_term_l term]
      exact descr_sub_complete st.ks st.fc trivial (by omega) sT sT fun _ _ _ h => h
    · exact descr_sub_complete st.ks st.fc trivial (by omega) sA sT (descr_incl sA fun v _ => toT v)
  · rcases ha with rfl | ⟨A, rfl, sA⟩
    · rw [subtype_term_l term]
      exact descr_sub_complete st.ks st.fc trivial (by omega) sT sB (descr_incl sT fun v _ => incl v (denD_term v))
    · exact descr_sub_complete st.ks st.fc trivial (by omega) sA sB (descr_incl sA incl)

theorem de_empty_sound (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {B : List (Term × Term)}
    (sB : DescrC Fn TF LF MF B) {m : Nat} (hm : K + 8 ≤ m)
    (h : Elixir.Module.Types.Descr.«empty?/1» (D m) (.map B) = .ok (boolAtom Bool.true)) :
    ∀ v : PtG TV LV MV FV, ¬denD (.map B) v := by
  obtain ⟨b, run, ex⟩ := de_empty st [] (Or.inr ⟨B, rfl, sB⟩)
  rw [empty_map_seen] at h
  have := bool_run (run m hm) h
  subst this
  exact (ex _ (Nat.lt_succ_self _) (safeN_nil _)).mp rfl

/-- Disjointness of element types of the next level: a uniform answer, sound. -/
theorem de_disj (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ s : Bool, (∀ m, K + 14 ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v : PtG TV LV MV FV, denD a v → denD b v → False) := by
  have hN : 0 < max (lh a) (lh b) + 1 := by omega
  obtain ⟨s, run⟩ := (st.ops hN).2.2.disj (st.nest ha (by omega)) (st.nest hb (by omega))
  refine ⟨s, run, fun st v hva hvb => ?_⟩
  subst st
  have h : Elixir.Module.Types.Descr.«disjoint?/2» (D (K + 14)) a b = .ok (boolAtom Bool.true) := run (K + 14) (by omega)
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [disjoint_term_l] at h
    rcases hb with rfl | ⟨B, rfl, sB⟩
    · rw [empty_term_false] at h; simp [boolAtom] at h
    · exact de_empty_sound st sB (by omega) h v hvb
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [disjoint_term_r] at h
    exact de_empty_sound st sA (by omega) h v hva
  have := descr_disj_sound st.ks st.fc trivial trivial (by omega) sA sB h v.1.1 v.1.2 v.2.2
  rw [(denD_map v).mp hva, (denD_map v).mp hvb] at this
  cases this

theorem de_resp (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {e e' : Term} {v : PtG TV LV MV FV} (he : DEG Fn TF LF MF e) (he' : DEG Fn TF LF MF e')
    (h : Term.compare (Term.fuel e e') e e' = .eq) (d : denD e' v) : denD e v := by
  rcases he with rfl | ⟨A, rfl, sA⟩
  · exact denD_term v
  rcases he' with rfl | ⟨B, rfl, sB⟩
  · obtain ⟨Y, e⟩ := map_cmp_shape h; cases e
  rw [denD_map] at d ⊢
  rw [descr_congr st.ks st.fc sA sB h v.1.1 v.1.2 v.2.2, d]

theorem noList_atom (M : List (Term × Term)) (name : String) :
    mapLookup (noList M) (.atom name) = if name = "list" then none else mapLookup M (.atom name) := by
  simp only [noList, mapLookup_filter, compareExact_eq_atom, Term.atom.injEq]

/-- Types without their list field. -/
theorem descr_noList {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) :
    DescrC Fn TF LF MF (noList X) ∧ lh (.map (noList X)) ≤ lh (.map X) ∧
      ∀ v : PtG TV LV MV FV, denD (.map (noList X)) v ↔ denD (.map X) v ∧ ¬tlD v := by
  have keys : ∀ q, (mapLookup (noList X) q).isSome → ∃ name ∈ names, q = .atom name := fun q h =>
    sX.keys q (by rw [← noList_lookup X q h]; exact h)
  refine ⟨⟨keys, fun name w h => ?_⟩, lh_descr_le keys fun name w h => ?_, fun v => ?_⟩
  · rw [noList_lookup X _ (by rw [h]; rfl)] at h; exact sX.fields name w h
  · rw [noList_lookup X _ (by rw [h]; rfl)] at h; exact lh_field_le h
  · rw [denD_map, denD_map, noList_atom]
    unfold tlD
    split <;> simp_all [dn_none]

theorem tailTerm_noList {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    (name : String) : mapLookup tailTerm (.atom name) = mapLookup (noList T) (.atom name) := by
  simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
  cases term
  rw [noList_atom]
  simp only [mapLookup, List.find?, tailTerm, compareExact_eq_atom, Term.atom.injEq]
  by_cases b : name = "bitmap" <;> by_cases t : name = "tuple" <;> by_cases f : name = "fun" <;>
    by_cases m : name = "map" <;> by_cases a : name = "atom" <;> by_cases l : name = "list" <;> simp_all

/-- `list_tail_unfold/1` of element types of the next level. -/
theorem de_tail (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {e : Term} (he : DEG Fn TF LF MF e) :
    ∃ e', (∀ d, Elixir.Module.Types.Descr.«list_tail_unfold/1» d e = .ok e') ∧ DEG Fn TF LF MF e' ∧
      (∀ v : PtG TV LV MV FV, denD e' v ↔ denD e v ∧ ¬tlD v) ∧ lh e' ≤ lh e := by
  rcases he with rfl | ⟨X, rfl, sX⟩
  · obtain ⟨T', run, look⟩ := tail_term_lookup
    obtain ⟨T, term, sT, -, lT, all⟩ := termC (FV := FV) st.ks st.ftop
    obtain ⟨sN, lN, semN⟩ := descr_noList (TV := TV) (LV := LV) (MV := MV) sT
    have eq : ∀ name, mapLookup T' (.atom name) = mapLookup (noList T) (.atom name) := fun name =>
      (look _).trans (tailTerm_noList term name)
    have keys : ∀ q, (mapLookup T' q).isSome → ∃ name ∈ names, q = .atom name := fun q h => by
      rw [look] at h
      rcases tailTerm_basic.keys q h with e | e | e | e | e | e <;> exact ⟨_, by simp [names], e⟩
    refine ⟨_, run, Or.inr ⟨T', rfl, keys, fun name w h => sN.fields name w (by rw [← eq]; exact h)⟩, fun v => ?_,
      lh_descr_le keys fun name w h => ?_⟩
    · rw [denD_map, eq, ← denD_map, semN v, denD_map, all _ v.2.1 _ v.2.2]
      simp [denD_term]
    · rw [eq] at h; have := lh_field_le h; rw [lh_term_zero]; omega
  · obtain ⟨sN, lN, semN⟩ := descr_noList (TV := TV) (LV := LV) (MV := MV) sX
    exact ⟨_, fun d => tail_map d X, Or.inr ⟨_, rfl, sN⟩, semN, lN⟩

end

end Elixir.STTDescrProofsTest.Nest
