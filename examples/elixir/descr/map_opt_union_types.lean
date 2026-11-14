namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized unions of map types on value maps. -/

/-- Map literals of element types, other than the top literal, keyed as Descr keys them. -/
def MLit (E : Term → Prop) (t : Term) : Prop := MapLitV E t ∧ ¬IsTop t ∧ KeyOk t

/-- Map types of element types: the top literal or BDDs of other literals. -/
abbrev MField (E : Term → Prop) (x : Term) : Prop := OField (MLit E) x

noncomputable def denMF (E : Term → Prop) (den : Term → V → Prop) (x : Term) (w : MW V) : Bool := denO x (valM E den w)

theorem mlit_not : ∀ t, MLit E t → ¬IsTop t := fun _ h => h.2.1

theorem denMF_exact {x y : Term} (fx : MField E x) (fy : MField E y) (e : compareExact (fuel y x) y x = .eq) (w : MW V) :
    denMF E den y w = denMF E den x w :=
  denO_exact mlit_not fx fy e (valM_resp w)

theorem EF.mopsE (ef : EF nd E V den tl K) : ElemOk E K :=
  ⟨ef.term, fun ha hb => let ⟨c, hc, run, _, _⟩ := ef.inter ha hb; ⟨c, hc, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha; ⟨b, run⟩, ef.none, ef.pos⟩

theorem EF.mdopsE (ef : EF nd E V den tl K) : ElemDiff E K :=
  ⟨fun ha hb => let ⟨c, hc, run, _, _⟩ := ef.diff ha hb; ⟨c, hc, run⟩⟩

theorem fieldsV_elem {l : List (Term × Term)} (h : FieldsV E l) : ElemFields E l := fun e me => (h.1 e me).2

theorem denMF_bdd {x : Term} (wx : Bdd (MLit E) x) (w : (MW V)) : denMF E den x w = eval (valM E den w) x := denO_bdd mlit_not wx _

theorem denMF_top (k : Term) (w : (MW V)) : denMF E den (.tuple #[k, .atom "open", .nil]) w = Bool.true := denO_top k _

/-- Leaves of map types hold the maps of their literal. -/
theorem denMF_leaf (ef : EF nd E V den tl K) {k : Int} {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) (g : TagV E tag)
    (w : (MW V)) : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w := by
  have lit : MapLitV E (.tuple #[.integer k, tag, fieldsTerm l]) := ⟨k, tag, l, rfl, g, sl⟩
  unfold denMF denO
  rw [eval_leaf, Bool.or_eq_true, valM_iff ef.mopsE ef.mdopsE ef.semR lit, nsem_lit]
  constructor
  · rintro (h | h)
    · unfold isOpenTop at h
      split at h
      · rename_i e
        simp only [Term.tuple.injEq] at e
        have e₁ := congrArg (fun a : Array Term => a[1]?) e
        have e₂ := congrArg (fun a : Array Term => a[2]?) e
        simp at e₁ e₂
        subst e₁
        rw [fieldsTerm_eq_nil.mp e₂]
        exact ⟨fun s => fsem_nil.mpr (Or.inl rfl), fun k i => Or.inl rfl⟩
      · cases h
    · exact h
  · exact Or.inr

theorem map_union_field {x y : Term} (hx : MField E x) (hy : MField E y) :
    ∃ r, Elixir.Module.Types.Descr.«map_union/2» x y = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w || denMF E den y w) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«map_union/2»; rfl, Or.inl ⟨k, rfl⟩,
      fun w => by simp [denMF_top]⟩
  rcases hy with ⟨k, rfl⟩ | wy
  · refine ⟨_, ?_, Or.inl ⟨k, rfl⟩, fun w => by simp [denMF_top]⟩
    unfold Elixir.Module.Types.Descr.«map_union/2»
    split
    · exact (not_top_of_ok wx mlit_not _ rfl).elim
    · rename_i e; simp at e; subst e; rfl
    · rename_i h; exact (h _ rfl).elim
  obtain ⟨r, hr, okr, semr⟩ := union_ok wx wy
  refine ⟨r, by rw [map_union_bdd (not_top_of_ok wx mlit_not) (not_top_of_ok wy mlit_not), hr],
    Or.inr (okr _ wx wy), fun w => ?_⟩
  rw [denMF_bdd (okr _ wx wy), denMF_bdd wx, denMF_bdd wy, semr _ (valM_resp w)]

/-- Leaves of map types are literals, the top one included. -/
theorem leafE {a b c : Term} (h : MField E (.tuple #[a, b, c])) :
    ∃ (k : Int) (l : List (Term × Term)), a = .integer k ∧ c = fieldsTerm l ∧
      TagV E b ∧ FieldsV E l ∧ KeyOk (.tuple #[a, b, c]) := by
  rcases h with ⟨k, e⟩ | w
  · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
    refine ⟨k, [], rfl, rfl, Or.inl rfl, ⟨by simp, by simp⟩, fun k' tag' l' e' => ?_⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_eq e'
    simp only [Term.atom.injEq] at e₂
    subst e₂
    exact ⟨fun h => by simp at h, fun _ ne => absurd (list_eq_nil.mp e₃.symm) ne⟩
  · rcases w.shape with e | e | ⟨k, x, y, e⟩ | ⟨_, _, _, _, _, e⟩
    · simp at e
    · simp at e
    · rw [e] at w
      obtain ⟨⟨k', tag, l, e', g, sl⟩, -, key⟩ := Bdd.leaf_iff.mp w
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_eq (e.trans e')
      subst e₂
      exact ⟨k', l, e₁, e₃, g, sl, e ▸ key⟩
    · simp at e

theorem leaf_field {k : Int} {tag : Term} {l : List (Term × Term)} (g : TagV E tag)
    (sl : FieldsV E l) (key : KeyOk (.tuple #[.integer k, tag, fieldsTerm l])) :
    MField E (.tuple #[.integer k, tag, fieldsTerm l]) := by
  by_cases top : tag = .atom "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, tag, l, rfl, g, sl⟩, fun ⟨k', e⟩ => top ?_, key⟩)
    obtain ⟨-, e₁, e₂⟩ := tuple3_eq e
    exact ⟨e₁, fieldsTerm_eq_nil.mp e₂⟩

theorem leaf_not_top {k : Int} {t : Term} {l : List (Term × Term)} (n : ¬(t = .atom "open" ∧ l = [])) {a : Term} :
    Term.tuple #[.integer k, t, fieldsTerm l] ≠ .tuple #[a, .atom "open", .nil] := by
  intro e
  simp only [Term.tuple.injEq] at e
  have e₁ := congrArg (fun a : Array Term => a[1]?) e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₁ e₂
  exact n ⟨e₁, fieldsTerm_eq_nil.mp e₂⟩

theorem tuple3_eq {a b c a' b' c' : Term} (h : Term.tuple #[a, b, c] = .tuple #[a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun x : Array Term => x[0]?) h
  have e₁ := congrArg (fun x : Array Term => x[1]?) h
  have e₂ := congrArg (fun x : Array Term => x[2]?) h
  simp at e₀ e₁ e₂
  exact ⟨e₀, e₁, e₂⟩

/-- Tags of which one has domains are not both atoms. -/
theorem atoms_guard {t₁ t₂ : Term} (g₁ : TagV E t₁) (g₂ : TagV E t₂) (h : ¬∃ s₁ s₂ : String, t₁ = .atom s₁ ∧ t₂ = .atom s₂) :
    Lynx.Except.andAlso (Erlang.erlang.«is_atom/1» t₁) (Erlang.erlang.«is_atom/1» t₂) = .ok (.atom "false") := by
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    first
      | exact absurd ⟨_, _, rfl, rfl⟩ h
      | (cases dl₁ <;> simp [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, fieldsTerm, Term.list] <;> done)
      | (cases dl₂ <;> simp [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, fieldsTerm, Term.list] <;> done)
      | (cases dl₁ <;> cases dl₂ <;> simp [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, fieldsTerm, Term.list])

/-- Optimized unions of map types hold the maps of either. -/
theorem opt_map_union_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {x y : Term} (hx : MField E x) (hy : MField E y)
    (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_map_union/3» (D m) x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w || denMF E den y w) := by
  obtain ⟨r₀, run₀, f₀, sem₀⟩ := map_union_field hx hy
  by_cases leaves : (∃ a b c, x = .tuple #[a, b, c]) ∧ (∃ a b c, y = .tuple #[a, b, c])
  · obtain ⟨⟨a₁, b₁, c₁, rfl⟩, ⟨a₂, b₂, c₂, rfl⟩⟩ := leaves
    obtain ⟨k₁, l₁, rfl, rfl, g₁, s₁, el₁⟩ := leafE hx
    obtain ⟨k₂, l₂, rfl, rfl, g₂, s₂, el₂⟩ := leafE hy
    by_cases n₁ : b₁ = .atom "open" ∧ l₁ = []
    · obtain ⟨rfl, rfl⟩ := n₁
      refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_map_union/3»; rfl, hx, fun w => ?_⟩
      have top := denMF_top (E := E) (den := den) (.integer k₁) w
      simp only [fieldsTerm, Term.list, List.map] at top ⊢
      rw [top]; rfl
    by_cases n₂ : b₂ = .atom "open" ∧ l₂ = []
    · obtain ⟨rfl, rfl⟩ := n₂
      refine ⟨_, ?_, hy, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · simp_all
        · rename_i h; exact (h (.integer k₂) (by simp [fieldsTerm, Term.list])).elim
      · have top := denMF_top (E := E) (den := den) (.integer k₂) w
        simp only [fieldsTerm, Term.list, List.map] at top ⊢
        rw [top]; simp
    have w₁ : Bdd (MLit E) (.tuple #[.integer k₁, b₁, fieldsTerm l₁]) :=
      hx.resolve_left fun ⟨k, e⟩ => leaf_not_top n₁ e
    have w₂ : Bdd (MLit E) (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) :=
      hy.resolve_left fun ⟨k, e⟩ => leaf_not_top n₂ e
    by_cases same : compareExact (fuel (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) (.tuple #[.integer k₁, b₁, fieldsTerm l₁])) (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) (.tuple #[.integer k₁, b₁, fieldsTerm l₁]) = .eq
    · refine ⟨_, ?_, hx, fun w => by rw [denMF_exact hx hy same, Bool.or_self]⟩
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rename_i heq; exact (leaf_not_top n₁ heq).elim
      · rename_i heq _; exact (leaf_not_top n₂ heq).elim
      simp only [leaf_guard]
      rw [ite_eq_left (by simpa using same)]
      rfl
    rcases opt_bdd_seen_map S (.atom "map_union") (.tuple #[.integer k₁, b₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, b₂, fieldsTerm l₂]) with seen | ⟨S', ok⟩
    · refine ⟨r₀, ?_, f₀, sem₀⟩
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rename_i heq; exact (leaf_not_top n₁ heq).elim
      · rename_i heq _; exact (leaf_not_top n₂ heq).elim
      simp only [leaf_guard]
      rw [ite_eq_right (by simpa using same)]
      simp [seen, run₀]
    have d₁ := fun w => denMF_leaf ef (k := k₁) s₁ g₁ w
    have d₂ := fun w => denMF_leaf ef (k := k₂) s₂ g₂ w
    -- leaves with domains are unioned as BDDs
    by_cases atoms : ¬∃ t₁ t₂ : String, b₁ = .atom t₁ ∧ b₂ = .atom t₂
    · refine ⟨r₀, ?_, f₀, sem₀⟩
      rw [← run₀, map_union_bdd (not_top_of_ok w₁ mlit_not) (not_top_of_ok w₂ mlit_not)]
      unfold Elixir.Module.Types.Descr.«opt_map_union/3»
      split
      · rename_i heq; exact (leaf_not_top n₁ heq).elim
      · rename_i heq _; exact (leaf_not_top n₂ heq).elim
      simp only [leaf_guard]
      rw [ite_eq_right (by simpa using same)]
      simp [ok, atoms_guard g₁ g₂ atoms]
    obtain ⟨t₁, t₂, rfl, rfl⟩ := Classical.not_not.mp atoms
    replace g₁ := g₁.of_atom
    replace g₂ := g₂.of_atom
    obtain ⟨st, run, strat⟩ := strat_val ef hm g₁ g₂ s₁ s₂ (fieldsV_elem s₁) (fieldsV_elem s₂) S'
    rcases strat with ⟨key, v₁, v₂, f, l, rfl, rf, rs, sl, el, sem⟩ | ⟨rfl, sub⟩ | ⟨rfl, sub⟩ | rfl
    · obtain ⟨len, sem⟩ := sem
      obtain ⟨k, hk, key⟩ := leaf_new_key t₁ g₁ (l.map fun e => .tuple #[e.1, e.2])
      refine ⟨.tuple #[.integer k, .atom t₁, fieldsTerm l], ?_, leaf_field (TagV.atom g₁) sl key, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        have hk' : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom t₁) (fieldsTerm l) =
            .ok (.tuple #[.integer k, .atom t₁, fieldsTerm l]) := hk
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, rf, rs, hk']
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, denMF_leaf ef sl (TagV.atom g₁) w, d₁, d₂]
        exact sem w
    · refine ⟨_, ?_, hy, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso]
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, d₁, d₂]
        exact ⟨Or.inr, fun h => h.elim (sub w) id⟩
    · refine ⟨_, ?_, hx, fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso]
      · apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, d₁, d₂]
        exact ⟨Or.inl, fun h => h.elim id (sub w)⟩
    · obtain ⟨r, hr, okr, semr⟩ := union_ok w₁ w₂
      refine ⟨r, ?_, Or.inr (okr _ w₁ w₂), fun w => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_map_union/3»
        split
        · rename_i heq; exact (leaf_not_top n₁ heq).elim
        · rename_i heq _; exact (leaf_not_top n₂ heq).elim
        simp only [leaf_guard]
        rw [ite_eq_right (by simpa using same)]
        simp [ok, run, Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, hr]
      · rw [denMF_bdd (okr _ w₁ w₂), denMF_bdd w₁, denMF_bdd w₂, semr _ (valM_resp w)]
  · refine ⟨r₀, ?_, f₀, sem₀⟩
    rw [opt_map_union_fallback _ _ _ _ (by
      by_cases h : ∃ a b c, x = .tuple #[a, b, c]
      · exact Or.inr fun a b c e => leaves ⟨h, a, b, c, e⟩
      · exact Or.inl fun a b c e => h ⟨a, b, c, e⟩)]
    exact run₀

end Elixir.STTDescrProofsTest.Nest
