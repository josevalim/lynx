namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! Optimized differences of map literals. -/

/-- `opt_map_difference_strategy/4` on literals of value maps. -/
theorem dstrat_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {l₁ l₂ : List (Term × Term)} (s₁ : FieldsV E l₁) (s₂ : FieldsV E l₂) :
    ∃ st, Elixir.Module.Types.Descr.«opt_map_difference_strategy/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂) (.atom t₁)
      (.atom t₂) = .ok st ∧ DRes E den t₁ t₂ st l₁ l₂ := by
  have walk := fun st inv => dwalk ef hm t₁ t₂ g₁ g₂ _ l₁ l₂ [] [] st (Nat.le_refl _) (by simpa using s₁)
    (by simpa using s₂) (by simp) inv
  by_cases tc : t₁ = t₂ ∨ t₂ = "open"
  · obtain ⟨st, run, res⟩ := walk (.atom "all_equal") (Or.inl ⟨rfl, tc, fun s tag o => Iff.rfl⟩)
    refine ⟨st, ?_, by simpa using res⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/4».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp_all [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, Lynx.Except.orElse, Erlang.erlang.«==/2»]
  · obtain ⟨st, run, res⟩ := walk (.atom "none") (Or.inr (Or.inr (Or.inr rfl)))
    refine ⟨st, ?_, by simpa using res⟩
    rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/4».eq_def]
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
      simp_all [Erlang.erlang.«is_atom/1», Lynx.Except.andAlso, Lynx.Except.orElse, Erlang.erlang.«==/2»]

/-- The general clause of `opt_map_leaf_difference/4`, which the single-key clause does not take. -/
theorem leaf_diff_general {d : Dispatcher} {S type : Term} {k₁ k₂ : Int} {t₁ t₂ : Term}
    {l₁ l₂ : List (Term × Term)} {st r : Term}
    (h : t₂ = .atom "open" → (∃ key f, l₂ = [(key, f)]) → type = .atom "union")
    (hs : Elixir.Module.Types.Descr.«opt_map_difference_strategy/4» d (fieldsTerm l₁) (fieldsTerm l₂) t₁ t₂ = .ok st)
    (hr : st = .atom "disjoint" ∧ r = .atom "disjoint" ∨ st = .atom "left_subtype_of_right" ∧ r = .atom "subtype" ∨
      st = .atom "none" ∧ r = .atom "none" ∨ ∃ key v₁ v₂, st = .tuple #[.atom "one_key_difference", key, v₁, v₂] ∧
        Elixir.Module.Types.Descr.«opt_map_leaf_one_key_difference/7» d t₁ (fieldsTerm l₁) key v₁ v₂ type S =
          .ok r) :
    Elixir.Module.Types.Descr.«opt_map_leaf_difference/4» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) type S = .ok r := by
  rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
  split
  · rename_i heq₁ heq₂
    obtain ⟨-, e₂, e₃⟩ := tuple3_eq heq₂
    have hl : ∃ key f, l₂ = [(key, f)] := by
      cases l₂ with
      | nil => simp [fieldsTerm, Term.list] at e₃
      | cons x xs =>
        cases xs with
        | nil =>
          simp [fieldsTerm, Term.list] at e₃
          exact ⟨x.1, x.2, by obtain ⟨k, f⟩ := x; simp⟩
        | cons y ys => simp [fieldsTerm, Term.list] at e₃
    have hu := h e₂ hl
    subst hu
    rw [e₃, e₂] at hs
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨key, v₁, v₂, rfl, run⟩ <;>
      simp [Erlang.erlang.«/=/2», *]
  · rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨key, v₁, v₂, rfl, run⟩ <;> simp [*]

theorem lookup_fieldValue {l : List (Term × Term)} (sl : FieldsV E l) {s : String} {f : Term}
    (h : mapLookup l (.atom s) = some f) : FieldValue E f := by
  obtain ⟨e, me, -, fe⟩ := lookup_some_mem h
  rw [← fe]; exact (sl.1 e me).2

/-- `opt_map_leaf_difference/4` compares map literals soundly. -/
theorem map_leaf_cmp (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a₁ a₂ type : Term) (S : List (Term × Term)) (ht : TypeOk type) (h₁ : MLit E a₁)
    (h₂ : MLit E a₂) :
    ∃ res, Elixir.Module.Types.Descr.«opt_map_leaf_difference/4» (D m) a₁ a₂ type (.map S) = .ok res ∧
      CmpOk (ValM E den) (MLit E) a₁ a₂ type res := by
  obtain ⟨⟨k₁, t₁, l₁, rfl, g₁, s₁⟩, n₁, key₁⟩ := h₁
  obtain ⟨⟨k₂, t₂, l₂, rfl, g₂, s₂⟩, n₂, key₂⟩ := h₂
  have nt₁ : ¬(t₁ = .atom "open" ∧ l₁ = []) := fun ⟨a, b⟩ => n₁ ⟨_, by rw [a, b]; rfl⟩
  have nt₂ : ¬(t₂ = .atom "open" ∧ l₂ = []) := fun ⟨a, b⟩ => n₂ ⟨_, by rw [a, b]; rfl⟩
  have v₁ := valM_leaf ef (k := k₁) s₁ g₁
  have v₂ := valM_leaf ef (k := k₂) s₂ g₂
  by_cases c1 : (t₂ = .atom "open" ∧ ∃ b f, l₂ = [(.atom b, f)]) ∧ type ≠ .atom "union"
  · obtain ⟨⟨rfl, b, f₂, rfl⟩, nu⟩ := c1
    obtain ⟨u₂, o₂, rfl, hu₂⟩ := (s₂.1 (.atom b, f₂) (by simp)).2
    have rel₂ : ∀ w, valM E den w (.tuple #[.integer k₂, .atom "open", fieldsTerm [(.atom b, .tuple #[u₂, boolAtom o₂])]]) =
        Bool.true ↔ FieldSem den (.tuple #[u₂, boolAtom o₂]) (w (.atom b)) := fun w => by rw [v₂, msem_one]
    have e2 : fieldsTerm [(Term.atom b, Term.tuple #[u₂, boolAtom o₂])] =
        .cons (.tuple #[.atom b, .tuple #[u₂, boolAtom o₂]]) .nil := rfl
    have tyc : type = .atom "none" ∨ type = .atom "intersection" := by
      rcases ht with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h nu
    have fnd := find_val b s₁
    cases hl : mapLookup l₁ (.atom b) with
    | none =>
      rw [hl] at fnd
      rcases g₁ with rfl | rfl | ⟨dl, rfl, dv⟩
      · have nn : fieldsTerm l₁ ≠ .nil := fun e => nt₁ ⟨rfl, fieldsTerm_eq_nil.mp e⟩
        refine ⟨.atom "none", ?_, Or.inr (Or.inr (Or.inr rfl))⟩
        rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
        simp only [e2]
        rcases tyc with rfl | rfl <;>
          simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            Erlang.erlang.«not/1», nn, Elixir.Module.Types.Descr.«map_key_tag_to_field/1»]
      · have absent : ∀ w, MSem den (.atom "closed") l₁ w → w (.atom b) = Option.none := fun w h => by
          rcases (fsem_none hl (w (.atom b))).mp (h b) with c | e
          · exact absurd c (by decide)
          · exact e
        cases o₂
        · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
          · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
            simp only [e2]
            rcases tyc with rfl | rfl <;>
              simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
                Erlang.erlang.«not/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember]
          · subst e
            apply Bool.eq_false_iff.mpr
            intro h
            rw [Bool.and_eq_true, v₁, rel₂] at h
            rw [absent w h.1, fieldSem_mk] at h
            simp at h
        · refine ⟨.atom "subtype", ?_, Or.inr (Or.inl ⟨rfl, fun ρ ⟨w, e⟩ h => ?_⟩)⟩
          · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
            simp only [e2]
            rcases tyc with rfl | rfl <;>
              simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
                Erlang.erlang.«not/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember]
          · subst e
            rw [v₁] at h
            rw [rel₂, absent w h, fieldSem_mk]
            simp
      · -- the default field of the domains at the key meets the field of the negated literal
        have gd : TagV E (fieldsTerm dl) := Or.inr (Or.inr ⟨dl, rfl, dv⟩)
        have hu₁ := tagType_value ef.mopsE gd "atom"
        have split := msem_split_absent ef gd hl
        obtain ⟨bd, rund, soundd⟩ := field_disj_bool ef hm (f₁ := tagField (fieldsTerm dl)) ⟨_, Bool.true, rfl, hu₁⟩
          ⟨u₂, o₂, rfl, hu₂⟩
        have ne : ∀ s, Erlang.erlang.«==/2» (fieldsTerm dl) (.atom s) = .ok (.atom "false") := fun s => by
          simp [Erlang.erlang.«==/2», fieldsTerm_ne_atom, Term.false]
        cases bd
        · obtain ⟨res, run, cmp⟩ := one_key_val ef hm gd s₁ nt₁ key₁ (k₁ := k₁) (o₁ := Bool.true)
            (.tuple #[.integer k₂, .atom "open", fieldsTerm [(.atom b, .tuple #[u₂, boolAtom o₂])]]) hu₁ hu₂ split type S
            (by rcases tyc with h | h <;> simp [h]) (fun w _ => rel₂ w) (fun h => absurd h nu)
          refine ⟨res, ?_, cmp⟩
          rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
          simp only [e2]
          simp [tagField, boolAtom] at run rund
          rcases tyc with rfl | rfl <;>
            simp [Erlang.erlang.«/=/2», fnd, ne, Lynx.Except.andAlso, key_tag_field gd, tagField,
              rund, boolAtom, run]
        · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
          · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
            simp only [e2]
            simp [tagField, boolAtom] at rund
            rcases tyc with rfl | rfl <;>
              simp [Erlang.erlang.«/=/2», fnd, ne, Lynx.Except.andAlso, key_tag_field gd, tagField,
                rund, boolAtom]
          · subst e
            apply Bool.eq_false_iff.mpr
            intro h
            rw [Bool.and_eq_true, v₁, rel₂, split] at h
            exact soundd rfl _ h.1.2 h.2
    | some f₁ =>
      rw [hl] at fnd
      obtain ⟨u₁, o₁, ef₁, hu₁⟩ := lookup_fieldValue s₁ hl
      subst ef₁
      obtain ⟨bd, rund, soundd⟩ := field_disj_bool ef hm ⟨u₁, o₁, rfl, hu₁⟩ ⟨u₂, o₂, rfl, hu₂⟩
      cases bd
      · obtain ⟨res, run, cmp⟩ := one_key_val ef hm g₁ s₁ nt₁ key₁ (k₁ := k₁)
          (.tuple #[.integer k₂, .atom "open", fieldsTerm [(.atom b, .tuple #[u₂, boolAtom o₂])]]) hu₁ hu₂ (msem_split hl) type S
          (by rcases tyc with h | h <;> simp [h]) (fun w _ => rel₂ w) (fun h => absurd h nu)
        refine ⟨res, ?_, cmp⟩
        rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
        simp only [e2]
        simp only [boolAtom] at run rund
        rcases g₁ with rfl | rfl | ⟨dl, rfl, -⟩ <;> rcases tyc with rfl | rfl <;>
          simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
            Erlang.erlang.«not/1», rund, boolAtom, run, fieldsTerm_ne_atom]
      · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
        · rw [Elixir.Module.Types.Descr.«opt_map_leaf_difference/4».eq_def]
          simp only [e2]
          simp only [boolAtom] at rund
          rcases g₁ with rfl | rfl | ⟨dl, rfl, -⟩ <;> rcases tyc with rfl | rfl <;>
            simp [Erlang.erlang.«/=/2», fnd, Erlang.erlang.«==/2», Lynx.Except.andAlso,
              Erlang.erlang.«not/1», rund, boolAtom, fieldsTerm_ne_atom]
        · subst e
          apply Bool.eq_false_iff.mpr
          intro h
          rw [Bool.and_eq_true, v₁, rel₂, msem_split hl] at h
          exact soundd rfl _ h.1.2 h.2
  · have h : t₂ = .atom "open" → (∃ key f, l₂ = [(key, f)]) → type = .atom "union" := by
      rintro ho ⟨key, f, rfl⟩
      obtain ⟨b, rfl⟩ := (s₂.1 (key, f) (by simp)).1
      exact Classical.byContradiction fun nu => c1 ⟨⟨ho, b, f, rfl⟩, nu⟩
    -- literals with domains have no strategy
    by_cases atoms : ¬∃ x₁ x₂ : String, t₁ = .atom x₁ ∧ t₂ = .atom x₂
    · have hs : Elixir.Module.Types.Descr.«opt_map_difference_strategy/4» (D m) (fieldsTerm l₁) (fieldsTerm l₂) t₁ t₂ =
          .ok (.atom "none") := by
        rw [Elixir.Module.Types.Descr.«opt_map_difference_strategy/4».eq_def]
        simp [atoms_guard g₁ g₂ atoms]
      exact ⟨_, leaf_diff_general h hs (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), Or.inr (Or.inr (Or.inr rfl))⟩
    obtain ⟨t₁, t₂, rfl, rfl⟩ := Classical.not_not.mp atoms
    have g₁' := g₁.of_atom
    have g₂' := g₂.of_atom
    obtain ⟨st, hs, dres⟩ := dstrat_val ef hm g₁' g₂' s₁ s₂
    rcases dres with ⟨rfl, s, hd⟩ | ⟨a, p₁, p₂, rfl, et, hp₁, hp₂, la₁, la₂, eqv⟩ | ⟨rfl, sub⟩ | rfl
    · refine ⟨_, leaf_diff_general h hs (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨rfl, fun ρ ⟨w, e⟩ => ?_⟩⟩
      subst e
      apply Bool.eq_false_iff.mpr
      intro hh
      rw [Bool.and_eq_true, v₁, v₂] at hh
      exact hd (w (.atom s)) (hh.1 s) (hh.2 s)
    · obtain ⟨u₁, o₁, rfl, hu₁⟩ := hp₁
      obtain ⟨u₂, o₂, rfl, hu₂⟩ := hp₂
      subst et
      have full : ∀ w, valM E den w (.tuple #[.integer k₂, .atom t₁, fieldsTerm l₂]) = Bool.true ↔
          MSemExcept den (.atom t₁) l₁ a w ∧ FieldSem den (.tuple #[u₂, boolAtom o₂]) (w (.atom a)) := by
        intro w
        rw [v₂, msem_split la₂]
        constructor
        · rintro ⟨⟨hs', hd⟩, ha⟩; exact ⟨⟨fun s ne => (eqv s ne t₁ (w (.atom s))).mpr (hs' s ne), hd⟩, ha⟩
        · rintro ⟨⟨hs', hd⟩, ha⟩; exact ⟨⟨fun s ne => (eqv s ne t₁ (w (.atom s))).mp (hs' s ne), hd⟩, ha⟩
      obtain ⟨res, run, cmp⟩ := one_key_val ef hm g₁ s₁ nt₁ key₁ (k₁ := k₁) _ hu₁ hu₂ (msem_split la₁) type S ht
        (fun w hw => by rw [full w, msem_split la₁] at *; exact ⟨fun h => h.2, fun h => ⟨hw.1, h⟩⟩)
        (fun _ => full)
      exact ⟨res, leaf_diff_general h hs (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, run⟩))), cmp⟩
    · refine ⟨_, leaf_diff_general h hs (Or.inr (Or.inl ⟨rfl, rfl⟩)), Or.inr (Or.inl ⟨rfl, fun ρ ⟨w, e⟩ hh => ?_⟩)⟩
      subst e
      rw [v₁] at hh
      rw [v₂]
      obtain ⟨v₀⟩ := ef.inhabited
      exact msem_of_atoms v₀ (fun s o => sub s o) hh
    · exact ⟨_, leaf_diff_general h hs (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), Or.inr (Or.inr (Or.inr rfl))⟩

theorem opt_map_seen {d : Dispatcher} {x y S : Term} (nx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) (ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq)
    (hs : Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_difference") x y = .ok (.atom "seen")) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d x y S = Elixir.Module.Types.Descr.«map_difference/2» x y := by
  rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
  split
  · exact absurd rfl (ny _)
  simp only [leaf_guard]
  split
  · rw [ite_eq_right (ne _ _ _ rfl)]
    split
    · exfalso; simp_all
    · exfalso; simp_all
    · simp [hs]
  · split
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
    · simp [hs]

theorem opt_map_ok {d : Dispatcher} {x y S S' : Term} (nx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) (ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq)
    (hs : Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_difference") x y = .ok (.tuple #[.atom "ok", S'])) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d x y S = Elixir.Module.Types.Descr.«bdd_difference/3» d x y
      (.function "Elixir.Module.Types.Descr" "-opt_map_difference/3-fun-0-" 3 #[S']) := by
  rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
  split
  · exact absurd rfl (ny _)
  simp only [leaf_guard]
  split
  · rw [ite_eq_right (ne _ _ _ rfl)]
    split
    · exfalso; simp_all
    · exfalso; simp_all
    · simp [hs]
  · split
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
    · simp [hs]

theorem opt_map_diff_same {d : Dispatcher} {S k a b y : Term} (ny : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_map_difference/3» d (.tuple #[k, a, b]) y S = .ok (.atom "bdd_bot") := by
  rw [Elixir.Module.Types.Descr.«opt_map_difference/3».eq_def]
  split
  · exact absurd rfl (ny _)
  simp only [leaf_guard]
  rw [ite_eq_left (by simpa using e)]
  rfl

/-- Optimized differences of map types hold the maps of the first and not the second. -/
theorem opt_map_diff_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {x y : Term} (fx : MField E x) (fy : MField E y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_map_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧
      (kept (.atom "map", w) = Bool.true → MField E w ∧ ∀ v, denMF E den w v = (denMF E den x v && !denMF E den y v)) ∧
      (kept (.atom "map", w) = Bool.false → ∀ v, (denMF E den x v && !denMF E den y v) = Bool.false) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«opt_map_difference/3»; rfl,
      fun kw => by simp [kept] at kw, fun _ v => by rw [denMF_top]; simp⟩
  rcases fx with ⟨k₀, rfl⟩ | wx
  · obtain ⟨w, run, k, d⟩ := map_neg_valK ef k₀ (m := n + 1) (by omega) (Or.inr wy) S
    exact ⟨w, run, fun kw => ⟨(k kw).1, fun v => by rw [(k kw).2 v, denMF_top]; simp⟩,
      fun kw v => by rw [d kw v]; simp⟩
  have wxV := wx
  have wyV := wy
  have nx := not_top_of_ok wxV mlit_not
  have ny := not_top_of_ok wyV mlit_not
  by_cases same : ∃ a b c, x = .tuple #[a, b, c] ∧ compareExact (fuel y x) y x = .eq
  · obtain ⟨a, b, c, rfl, e⟩ := same
    exact ⟨_, opt_map_diff_same ny e, fun kw => by simp [kept] at kw, fun _ v => by
      rw [denMF_exact (Or.inr wxV) (Or.inr wyV) e, Bool.and_not_self]⟩
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := fun a b c ex e => same ⟨a, b, c, ex, e⟩
  rcases opt_bdd_seen_map S (.atom "map_difference") x y with seen | ⟨S', ok⟩
  · obtain ⟨w, run, fw, sem⟩ := map_diff_val (Or.inr wxV) (Or.inr wyV)
    refine ⟨w, by rw [opt_map_seen nx ny ne seen, run], fun _ => ⟨fw, sem⟩, fun kw v => ?_⟩
    rw [← sem v]
    rcases fw with ⟨k', rfl⟩ | ww
    · simp [kept] at kw
    · rw [denMF_bdd ww]; exact drop_bdd ww kw _
  · obtain ⟨r, hr, okr, semr⟩ := diff3_ok valM_respM (d := D (n + 1))
      (cmp := .function "Elixir.Module.Types.Descr" "-opt_map_difference/3-fun-0-" 3 #[.map S'])
      (fun a₁ a₂ type ht h₁ h₂ => by
        obtain ⟨res, run, cmp⟩ := map_leaf_cmp ef (m := n) hn a₁ a₂ type S' ht h₁ h₂
        refine ⟨res, ?_, cmp⟩
        rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_map_difference/3-fun-0-/3».pure]
        simpa [Elixir.Module.Types.Descr.«-opt_map_difference/3-fun-0-/4»] using run)
      _ y wyV (fun _ h => h) x wxV
    have sem : ∀ v, denMF E den r v = (denMF E den x v && !denMF E den y v) := fun v => by
      rw [denMF_bdd okr, denMF_bdd wxV, denMF_bdd wyV, semr _ ⟨v, rfl⟩]
    refine ⟨r, by rw [opt_map_ok nx ny ne ok, hr], fun _ => ⟨Or.inr okr, sem⟩, fun kw v => ?_⟩
    rw [← sem v, denMF_bdd okr]; exact drop_bdd okr kw _

end Elixir.STTDescrProofsTest.Nest
