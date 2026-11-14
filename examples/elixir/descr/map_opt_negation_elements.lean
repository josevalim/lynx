namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized negations of map types of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem msem_one {a : String} {f : Term} {w : MW V} : MSem den (.atom "open") [(.atom a, f)] w ↔ FieldSem den f (w (.atom a)) := by
  constructor
  · intro h; simpa [FSem, TagSem, lookup_cons_atom] using h a
  · intro h
    refine ⟨fun s => ?_, fun k i => Or.inl rfl⟩
    unfold FSem TagSem
    rw [lookup_cons_atom]
    by_cases e : a = s
    · subst e; simpa using h
    · simp [e, mapLookup]

theorem fieldsV_one {a : String} {f : Term} (hf : FieldValue E f) : FieldsV E [(.atom a, f)] :=
  ⟨fun e me => by simp at me; subst me; exact ⟨⟨a, rfl⟩, hf⟩, by simp⟩

theorem denMF_one (ef : EF nd E V den tl K) {H : Int} {a : String} {f : Term} (hf : FieldValue E f) (w : MW V) :
    denMF E den (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, f)]]) w = Bool.true ↔ FieldSem den f (w (.atom a)) := by
  rw [denMF_leaf ef (fieldsV_one hf) (Or.inl rfl), msem_one]

/-- Open maps of one field of an element type, with a key that is not negative. -/
theorem one_field (_ef : EF nd E V den tl K) {H : Int} {a : String} {c : Term} {o : Bool} (hH : 0 ≤ H) (hc : E c) :
    MField E (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom o])]]) := by
  refine leaf_field (Or.inl rfl) (fieldsV_one ⟨c, o, rfl, hc⟩) fun k tag l e => ?_
  obtain ⟨e₁, e₂, -⟩ := tuple3_eq e
  simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
  subst e₁ e₂
  exact ⟨fun h => by simp at h, fun _ _ => hH⟩

/-- Element types decide their emptiness exactly. -/
theorem EF.empty1 (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {c : Term} (hc : E c) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty?/1» (D m) c = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ v, ¬den c v) := by
  obtain ⟨b, run, sem⟩ := ef.empty [] hc
  rcases ef.static hc with rfl | ⟨C, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«empty?/1», boolAtom], ?_⟩
    obtain ⟨v⟩ := ef.inhabited
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => h v (ef.den_term v)
  · exact ⟨b, by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm,
      sem (lh (.map C) + 1) (Nat.lt_succ_self _) (safeN_nil _)⟩
  · exact ⟨b, by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm,
      sem (lh (.tuple #[.reference r₀, .map st₀, g₀]) + 1) (Nat.lt_succ_self _) (safeN_nil _)⟩

theorem fieldSem_compl {t c : Term} {o : Bool} (sem : ∀ v, den c v ↔ ¬den t v) (x : Option V) :
    FieldSem den (.tuple #[c, boolAtom (!o)]) x ↔ ¬FieldSem den (.tuple #[t, boolAtom o]) x := by
  rw [fieldSem_mk, fieldSem_mk]
  cases x with
  | none => cases o <;> simp
  | some y => simp [sem y]

/-- Optimized negations of map types. -/
theorem map_neg_valK (ef : EF nd E V den tl K) (k₀ : Int) {m : Nat} (hm : K + 1 ≤ m) {x : Term}
    (fx : MField E x) (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_map_difference/3» (D m) (.tuple #[.integer k₀, .atom "open", .nil]) x (.map S) = .ok w ∧
      (kept (.atom "map", w) = Bool.true → MField E w ∧ ∀ v, denMF E den w v = !denMF E den x v) ∧
      (kept (.atom "map", w) = Bool.false → ∀ v, denMF E den x v = Bool.true) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«opt_map_difference/3»; rfl,
      fun k => by simp [kept] at k, fun _ v => denMF_top (E := E) (den := den) _ v⟩
  have wE : Bdd (MLit E) x := wx
  -- plain negations
  have plain : ∀ (arr : Array Term), x = .tuple arr →
      (∀ k key f, x ≠ .tuple #[k, .atom "open", .cons (.tuple #[key, f]) .nil]) →
      ∃ w, Elixir.Module.Types.Descr.«opt_map_difference/3» (D m) (.tuple #[.integer k₀, .atom "open", .nil]) x (.map S) = .ok w ∧
        (kept (.atom "map", w) = Bool.true → MField E w ∧ ∀ v, denMF E den w v = !denMF E den x v) ∧
        (kept (.atom "map", w) = Bool.false → ∀ v, denMF E den x v = Bool.true) := by
    intro arr hx none
    obtain ⟨w, run, keep, sem, nl⟩ := neg_okN wx
    have ww := keep _ wx
    refine ⟨w, by rw [opt_neg_plainK k₀ (D m) _ arr hx (not_top_of_ok wE mlit_not) none, run], fun _ => ⟨Or.inr ww, fun v => by
        rw [denMF_bdd ww, denMF_bdd wE, sem _ (valM_resp v)]⟩, fun kw v => ?_⟩
    rw [denMF_bdd wE]
    exact neg_drop (sem _ (valM_resp v)) (drop_bdd ww kw _)
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k, fun _ v => by simp [denMF_bdd wE]⟩
    rcases opt_bdd_seen_map S (.atom "map_difference") (.tuple #[.integer k₀, .atom "open", .nil]) (.atom "bdd_top") with seen | ⟨S', ok⟩
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [seen, Elixir.Module.Types.Descr.«map_difference/2», Elixir.Module.Types.Descr.«bdd_difference/2»,
        Erlang.erlang.«=:=/2»]
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [ok]
      unfold Elixir.Module.Types.Descr.«bdd_difference/3»
      simp [Elixir.Module.Types.Descr.«bdd_difference/2», Erlang.erlang.«=:=/2»]
  · refine ⟨(.tuple #[.integer k₀, .atom "open", .nil]), ?_, fun _ => ⟨Or.inl ⟨_, rfl⟩, fun v => by simp [denMF_top, denMF_bdd wE]⟩,
      fun k => by simp [kept] at k⟩
    rcases opt_bdd_seen_map S (.atom "map_difference") (.tuple #[.integer k₀, .atom "open", .nil]) (.atom "bdd_bot") with seen | ⟨S', ok⟩
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [seen, Elixir.Module.Types.Descr.«map_difference/2», Elixir.Module.Types.Descr.«bdd_difference/2»,
        Erlang.erlang.«=:=/2»]
    · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
      simp [ok]
      unfold Elixir.Module.Types.Descr.«bdd_difference/3»
      simp [Elixir.Module.Types.Descr.«bdd_difference/2», Erlang.erlang.«=:=/2»]
  · obtain ⟨l, rfl, g, sl, nt, -, -⟩ := mlit_leaf (Bdd.leaf_iff.mp wx)
    by_cases one : ∃ key f, a = .atom "open" ∧ l = [(key, f)]
    · obtain ⟨key, f, rfl, rfl⟩ := one
      obtain ⟨a, ka⟩ := (sl.1 (key, f) (by simp)).1
      simp only at ka
      subst ka
      obtain ⟨t, o, eft, ht⟩ := (sl.1 (.atom a, f) (by simp)).2
      simp only at eft
      subst eft
      have fx := denMF_one ef (H := k) (a := a) (f := .tuple #[t, boolAtom o]) ⟨t, o, rfl, ht⟩
      rcases opt_bdd_seen_map S (.atom "map_difference") (.tuple #[.integer k₀, .atom "open", .nil])
        (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[t, boolAtom o])]]) with seen | ⟨S', ok⟩
      · obtain ⟨w, run, keep, sem, nl⟩ := neg_okN wx
        have ww := keep _ wx
        refine ⟨w, ?_, fun _ => ⟨Or.inr ww, fun v => by
          rw [denMF_bdd ww, denMF_bdd wE, sem _ (valM_resp v)]⟩, fun kw v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
          simp only [fieldsTerm, List.map, Term.list] at seen ⊢
          simp only [leaf_guard, cons_ne_top3, ite_false]
          simp [seen]
          exact (map_difference_neg (not_top_of_ok wE mlit_not) _ rfl).trans run
        · rw [denMF_bdd wE]
          exact neg_drop (sem _ (valM_resp v)) (drop_bdd ww kw _)
      · obtain ⟨c, hc, runc, semc'⟩ := ef.opt_diff S' ef.term ht (show K ≤ m by omega)
        have semc : ∀ v, den c v ↔ ¬den t v := fun v => by simp [semc' v, ef.den_term]
        have fd : Elixir.Module.Types.Descr.«field_opt_difference/3» (D m) (.tuple #[.atom "term", .atom "true"])
            (.tuple #[t, boolAtom o]) (.map S') = .ok (.tuple #[c, boolAtom (!o)]) := by
          simp only [Elixir.Module.Types.Descr.«field_opt_difference/3», runc]
          cases o <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
        have compl := fieldSem_compl (o := o) semc
        have leafCase : ∃ H : Int, 0 ≤ H ∧
            Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "open") (Term.list [.tuple #[.atom a, .tuple #[c, boolAtom (!o)]]]) =
              .ok (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom (!o)])]]) :=
          leaf_one_open _ _
        obtain ⟨H, hH, leaf⟩ := leafCase
        have leafSem : ∀ v, denMF E den (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom (!o)])]]) v =
            !denMF E den (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[t, boolAtom o])]]) v := by
          intro v
          apply Bool.eq_iff_iff.mpr
          rw [denMF_one ef (f := .tuple #[c, boolAtom (!o)]) ⟨c, !o, rfl, hc⟩, Bool.not_eq_true', ← Bool.not_eq_true, fx, compl]
        have leafNeg : MField E (.tuple #[.integer H, .atom "open", fieldsTerm [(.atom a, .tuple #[c, boolAtom (!o)])]]) :=
          one_field ef hH hc
        simp only [fieldsTerm, List.map, Term.list] at ok leaf
        cases o
        · simp only [boolAtom, Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at ok leaf fd
          refine ⟨_, ?_, fun _ => ⟨leafNeg, leafSem⟩, fun kw => by simp [kept] at kw⟩
          unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
          simp only [fieldsTerm, List.map, Term.list] at ok leaf ⊢
          simp only [leaf_guard, cons_ne_top3, ite_false]
          simp [ok, fd, Elixir.Module.Types.Descr.«field_empty?/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember, leaf]
        · obtain ⟨b, runb, semb⟩ := ef.empty1 (show K ≤ m by omega) hc
          simp only [boolAtom, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at ok leaf fd
          cases b
          · refine ⟨_, ?_, fun _ => ⟨leafNeg, leafSem⟩, fun kw => by simp [kept] at kw⟩
            unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
            simp only [fieldsTerm, List.map, Term.list] at ok leaf ⊢
            simp only [leaf_guard, cons_ne_top3, ite_false]
            simp [ok, fd, Elixir.Module.Types.Descr.«field_empty?/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember, leaf,
              runb]
          · refine ⟨.atom "bdd_bot", ?_, fun kw => by simp [kept] at kw, fun _ v => ?_⟩
            · unfold Elixir.Module.Types.Descr.«opt_map_difference/3»
              simp only [fieldsTerm, List.map, Term.list] at ok ⊢
              simp only [leaf_guard, cons_ne_top3, ite_false]
              simp [ok, fd, Elixir.Module.Types.Descr.«field_empty?/1», Elixir.Module.Types.Descr.«map_key_tag_to_field/1», boolAtom, isMember, runb]
            · rw [fx, fieldSem_mk]
              cases e : v (.atom a) with
              | none => exact Or.inl ⟨rfl, rfl⟩
              | some y =>
                refine Or.inr ⟨y, rfl, ?_⟩
                exact Classical.byContradiction fun h => (semb.mp rfl) y ((semc y).mpr h)
    · exact plain _ rfl fun k' key f e => one ⟨key, f, by
        simp only [Term.tuple.injEq] at e
        have e₁ := congrArg (fun a : Array Term => a[1]?) e
        have e₂ := congrArg (fun a : Array Term => a[2]?) e
        simp at e₁ e₂
        refine ⟨e₁, ?_⟩
        cases l with
        | nil => simp [fieldsTerm, Term.list] at e₂
        | cons x xs =>
          cases xs with
          | nil =>
            simp [fieldsTerm, Term.list] at e₂ ⊢
            obtain ⟨k₁, k₂⟩ := e₂
            exact Prod.ext k₁ k₂
          | cons y ys => simp [fieldsTerm, Term.list] at e₂⟩
  · exact plain _ rfl fun _ _ _ e => by simp at e

end Elixir.STTDescrProofsTest.Nest
