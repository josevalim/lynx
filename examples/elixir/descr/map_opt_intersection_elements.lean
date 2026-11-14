namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of map types of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types decide their emptiness exactly from an empty seen set. -/
theorem EF.msemZ (ef : EF nd E V den tl K) : ElemSem E K V den (fun S => S = []) where
  term := ef.den_term
  inter := ef.semR.inter
  diff := ef.semR.diff
  empty := fun {a S m b} ha hS hm run => by
    subst hS
    obtain ⟨b', run', h⟩ := ef.empty [] ha
    rw [run' _ hm] at run
    have : b' = b := by cases b <;> cases b' <;> simp_all [boolAtom]
    subst this
    exact h (lh a + 1) (Nat.lt_succ_self _) (safeN_nil _)
  inhabited := ef.inhabited
  resp := ef.semR.resp

theorem opt_ifun (ef : EF nd E V den tl K) (S : List (Term × Term)) : IFun E den (K + 1) (optMapIFun (.map S)) := by
  intro m hm a b ha hb
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S ha hb hn
  refine ⟨c, hc, sem, ?_⟩
  rw [optMapIFun, Erlang.program.«Elixir.Module.Types.Descr:-opt_map_leaf_intersection/3-fun-0-/2».pure]
  simpa [Elixir.Module.Types.Descr.«-opt_map_leaf_intersection/3-fun-0-/3»] using run

/-- `map_closed_subtype_of_open?/2` returns a Boolean, and `true` only when the closed fields allow less than the
open ones. -/
theorem cso_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
    FieldsV E l₁ → FieldsV E l₂ → ∃ c : Bool,
      Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l₁) (fieldsTerm l₂) =
        .ok (boolAtom c) ∧ (c = Bool.true → ∀ s o, FSem den (.atom "closed") l₁ s o → FSem den (.atom "open") l₂ s o) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨Bool.true, ?_, fun _ s o _ => fsem_nil.mpr (Or.inl rfl)⟩
    rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
    simp [fieldsTerm, Term.list, boolAtom]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₂ with
    | [] =>
      refine ⟨Bool.true, ?_, fun _ s o _ => fsem_nil.mpr (Or.inl rfl)⟩
      rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
      cases l₁ <;> simp [fieldsTerm, Term.list, boolAtom]
    | (k₂, f₂) :: t₂ =>
      obtain ⟨b, rfl⟩ := (h₂.1 _ List.mem_cons_self).1
      obtain ⟨u₂, o₂, rfl, hu₂⟩ := (h₂.1 _ List.mem_cons_self).2
      have s₂ := fieldsV_tail h₂
      have hd₂ := fieldsV_head h₂
      simp only [List.length_cons] at size
      -- the key of the open literal missing from the closed one
      have missing : ∀ (l : List (Term × Term)), (∀ e ∈ l, Term.compare (Term.fuel (.atom b) e.1) (.atom b) e.1 = .lt) → FieldsV E l →
          l.length + t₂.length ≤ N →
          (Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l) (fieldsTerm t₂) =
            Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l)
              (fieldsTerm ((.atom b, .tuple #[u₂, boolAtom o₂]) :: t₂)) →
            True) →
          ∃ c : Bool, Lynx.Except.andAlso (pure (boolAtom o₂))
              (Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2» (D m) (fieldsTerm l) (fieldsTerm t₂))
              Bool.true = .ok (boolAtom c) ∧
            (c = Bool.true → ∀ s o, FSem den (.atom "closed") l s o →
              FSem den (.atom "open") ((.atom b, .tuple #[u₂, boolAtom o₂]) :: t₂) s o) := by
        intro l above sl sz _
        obtain ⟨c, run, sound⟩ := ih l t₂ sz sl s₂
        refine ⟨o₂ && c, ?_, fun e s o h => ?_⟩
        · cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, run]
        · simp only [Bool.and_eq_true] at e
          obtain ⟨rfl, ec⟩ := e
          by_cases bs : b = s
          · subst bs
            rw [fsem_cons_self, fieldSem_mk]
            rw [fsem_none (lookup_above above)] at h
            rcases h with h | h
            · exact absurd h (by decide)
            · exact Or.inl ⟨h, rfl⟩
          · rw [fsem_cons_ne bs]
            exact sound ec s o h
      rcases l₁ with _ | ⟨⟨k₁, f₁⟩, t₁⟩
      · obtain ⟨c, run, sound⟩ := missing [] (by simp) ⟨by simp, by simp⟩ (by simp; omega) (fun _ => trivial)
        refine ⟨c, ?_, sound⟩
        rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
        simpa [fieldsTerm, Term.list] using run
      · simp only [List.length_cons] at size
        obtain ⟨a, rfl⟩ := (h₁.1 _ List.mem_cons_self).1
        obtain ⟨u₁, o₁, rfl, hu₁⟩ := (h₁.1 _ List.mem_cons_self).2
        have s₁ := fieldsV_tail h₁
        have hd₁ := fieldsV_head h₁
        rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
        · obtain ⟨c, run, sound⟩ := ih t₁ _ (by simp; omega) s₁ h₂
          refine ⟨c, ?_, fun e s o h => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp] at run ⊢
            exact run
          · by_cases as : a = s
            · subst as
              have above : ∀ y ∈ (Term.atom b, Term.tuple #[u₂, boolAtom o₂]) :: t₂, Term.compare (Term.fuel (.atom a) y.1) (.atom a) y.1 = .lt := by
                intro y my
                rcases List.mem_cons.mp my with rfl | my
                · exact cmp
                · exact cmp_lt_trans cmp (hd₂ y my)
              exact (fsem_none (lookup_above above) o).mpr (Or.inl rfl)
            · rw [fsem_cons_ne as] at h
              exact sound e s o h
        · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
          subst ab
          obtain ⟨c₁, run₁, sound₁⟩ := field_sub_bool ef hm ⟨u₁, o₁, rfl, hu₁⟩ ⟨u₂, o₂, rfl, hu₂⟩
          obtain ⟨c, run, sound⟩ := ih t₁ t₂ (by omega) s₁ s₂
          refine ⟨c₁ && c, ?_, fun e s o h => ?_⟩
          · rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
            have notLt : ¬(Term.compare (Term.fuel (.atom a) (.atom a)) (.atom a) (.atom a)).isLT = Bool.true := by simp
            simp only [fieldsTerm, Term.list, List.map] at run ⊢
            cases c₁ <;> simp [Erlang.erlang.«</2», Erlang.erlang.«=:=/2», run₁, run]
          · simp only [Bool.and_eq_true] at e
            by_cases as : a = s
            · subst as
              rw [fsem_cons_self] at h ⊢
              exact sound₁ e.1 o h
            · rw [fsem_cons_ne as] at h ⊢
              exact sound e.2 s o h
        · have cmp' : Term.compare (Term.fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .lt := Lynx.Term.compare_gt_iff_lt.mp cmp
          have above : ∀ y ∈ (Term.atom a, Term.tuple #[u₁, boolAtom o₁]) :: t₁, Term.compare (Term.fuel (.atom b) y.1) (.atom b) y.1 = .lt := by
            intro y my
            rcases List.mem_cons.mp my with rfl | my
            · exact cmp'
            · exact cmp_lt_trans cmp' (hd₁ y my)
          obtain ⟨c, run, sound⟩ := missing _ above h₁ (by simp; omega) (fun _ => trivial)
          refine ⟨c, ?_, sound⟩
          rw [Elixir.Module.Types.Descr.«map_closed_subtype_of_open?/2».eq_def]
          have ne : ¬compareExact (fuel (.atom b) (.atom a)) (.atom b) (.atom a) = .eq := by
            intro e
            have := (atom_compareExact_eq b (.atom a)).mp e
            simp at this
            subst this
            exact cmp_lt_ne cmp' rfl
          have ba : ¬b = a := fun h => by subst h; exact cmp_lt_ne cmp' rfl
          simp only [fieldsTerm, Term.list, List.map] at run ⊢
          simp [Erlang.erlang.«</2», Erlang.erlang.«=:=/2», cmp, ba]
          simpa using run

theorem inter_plainM {x y : Term} (wx : Bdd (MLit E) x) (wy : Bdd (MLit E) y) :
    ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x y = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
  obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
  refine ⟨r, by rw [map_intersection_bdd (not_top_of_ok wx mlit_not) (not_top_of_ok wy mlit_not), hr],
    Or.inr (okr _ wx wy), fun w => ?_⟩
  rw [denMF_bdd (okr _ wx wy), denMF_bdd wx, denMF_bdd wy, semr _ (valM_resp w)]

theorem mlit_leaf {k : Int} {a b : Term} (h : MLit E (.tuple #[.integer k, a, b])) :
    ∃ l : List (Term × Term), b = fieldsTerm l ∧ TagV E a ∧ FieldsV E l ∧ ¬(a = .atom "open" ∧ l = []) ∧
      (a = .atom "open" → 0 ≤ k) ∧ (a = .atom "closed" → k < 0) := by
  obtain ⟨⟨k', t, l, e, g, sl⟩, nt, key⟩ := h
  obtain ⟨e₀, e₁, e₂⟩ := tuple3_eq e
  simp only [Term.integer.injEq] at e₀
  subst e₀ e₁ e₂
  refine ⟨l, rfl, g, sl, fun ⟨o, n⟩ => nt ⟨_, by rw [o, n]; rfl⟩, fun o => ?_, fun c => ?_⟩
  · subst o
    have kk := key k "open" (l.map fun e => .tuple #[e.1, e.2]) rfl
    refine kk.2 rfl fun ne => nt ⟨.integer k, ?_⟩
    have : l = [] := by cases l <;> simp_all
    subst this; rfl
  · subst c
    exact (key k "closed" (l.map fun e => .tuple #[e.1, e.2]) rfl).1 rfl

/-- New map leaves get the keys Descr gives them, whatever their tag. -/
theorem leaf_new_keyM {tag : Term} (g : TagV E tag) (l : List Term) :
    ∃ k : Int, Elixir.Module.Types.Descr.«bdd_leaf_new/2» tag (Term.list l) =
      .ok (.tuple #[.integer k, tag, Term.list l]) ∧ KeyOk (.tuple #[.integer k, tag, Term.list l]) := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · exact leaf_new_key "open" (Or.inl rfl) l
  · exact leaf_new_key "closed" (Or.inr rfl) l
  · obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (fieldsTerm dl) (Term.list l))
    refine ⟨min (l.length : Int) 2147483647 * 134217728 + hash, ?_, fun k tag l' e => ?_⟩
    · have ne := fieldsTerm_ne_atom dl "closed"
      generalize fieldsTerm dl = T at ne hrun ⊢
      unfold Elixir.Module.Types.Descr.«bdd_leaf_new/2»
      split
      · exact absurd rfl ne
      · simp [hrun, leaf_key_val]
    · obtain ⟨-, e₂, -⟩ := tuple3_eq e
      exact absurd e₂ (fieldsTerm_ne_atom dl tag)

/-- The clause of `opt_map_intersection/3` for two leaves that are not all maps. -/
theorem opt_map_inter_leavesG {d : Dispatcher} {S : Term} {k₁ k₂ : Int} {t₁ t₂ : Term}
    {l₁ l₂ : List (Term × Term)} (n₁ : ¬(t₁ = .atom "open" ∧ l₁ = [])) (n₂ : ¬(t₂ = .atom "open" ∧ l₂ = []))
    (ne : compareExact (fuel (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁])) (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) ≠ .eq) :
    (Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_intersection") (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
        (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
        (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S =
        Elixir.Module.Types.Descr.«map_intersection/2» (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
          (.tuple #[.integer k₂, t₂, fieldsTerm l₂])) ∧
    (∀ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "map_intersection")
        (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) =
        .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
        (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S =
        Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
          (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S') := by
  constructor <;> intros <;>
  · unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
    split
    · rename_i heq; exact (leaf_not_top n₁ heq).elim
    · rename_i heq _; exact (leaf_not_top n₂ heq).elim
    simp only [leaf_guard]
    rw [ite_eq_right (by simpa using ne)]
    simp_all

/-- Exactly equal map leaves intersect to the first. -/
theorem opt_map_inter_sameG {d : Dispatcher} {S : Term} {k₁ k₂ : Int} {t₁ t₂ : Term}
    {l₁ l₂ : List (Term × Term)} (n₁ : ¬(t₁ = .atom "open" ∧ l₁ = [])) (n₂ : ¬(t₂ = .atom "open" ∧ l₂ = []))
    (e : compareExact (fuel (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁])) (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) = .eq) :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[.integer k₁, t₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, t₂, fieldsTerm l₂]) S = .ok (.tuple #[.integer k₁, t₁, fieldsTerm l₁]) := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  · rename_i heq; exact (leaf_not_top n₁ heq).elim
  · rename_i heq _; exact (leaf_not_top n₂ heq).elim
  simp only [leaf_guard]
  rw [ite_eq_left (by simpa using e)]
  rfl

theorem opt_map_inter_top_eqG {d : Dispatcher} {x S : Term} {k : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d x (.tuple #[k, .atom "open", .nil]) S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  · exact (hx _ rfl).elim
  · rfl
  all_goals rename_i h
  all_goals first | exact (h _ rfl).elim | (exfalso; simp_all)

theorem opt_map_inter_plain_eqG {d : Dispatcher} {x y S : Term} (tx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ty : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (h3 : ∀ a b c a' b' c', x = .tuple #[a, b, c] → y = .tuple #[a', b', c'] → False)
    (h4 : ∀ k fo a b c u e, x = .tuple #[k, .atom "open", fo] → y = .tuple #[a, b, c, u, e] → False)
    (h5 : ∀ k fo a b c u e, y = .tuple #[k, .atom "open", fo] → x = .tuple #[a, b, c, u, e] → False) :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d x y S = Elixir.Module.Types.Descr.«map_intersection/2» x y := by
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := by
    rintro a b c rfl e
    obtain ⟨_, _, _, rfl, -⟩ := exact_tuple3 e
    exact h3 _ _ _ _ _ _ rfl rfl
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
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

theorem opt_map_inter_push_lG {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[k, .atom "open", fo]) (.tuple #[h, lit, c, u, e]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function "Elixir.Module.Types.Descr" "map_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

theorem opt_map_inter_push_rG {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_map_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function "Elixir.Module.Types.Descr" "map_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

/-- Optimized intersections of map literals hold the maps of both. -/
theorem leaf_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {k₁ k₂ : Int} {a₁ b₁ a₂ b₂ : Term}
    (lx : MLit E (.tuple #[.integer k₁, a₁, b₁])) (ly : MLit E (.tuple #[.integer k₂, a₂, b₂]))
    (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) (.tuple #[.integer k₁, a₁, b₁])
        (.tuple #[.integer k₂, a₂, b₂]) (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den (.tuple #[.integer k₁, a₁, b₁]) w &&
        denMF E den (.tuple #[.integer k₂, a₂, b₂]) w) := by
  obtain ⟨l₁, rfl, g₁, s₁, n₁, -, c₁⟩ := mlit_leaf lx
  obtain ⟨l₂, rfl, g₂, s₂, n₂, -, c₂⟩ := mlit_leaf ly
  by_cases same : compareExact (fuel (.tuple #[.integer k₂, a₂, fieldsTerm l₂]) (.tuple #[.integer k₁, a₁, fieldsTerm l₁])) (.tuple #[.integer k₂, a₂, fieldsTerm l₂]) (.tuple #[.integer k₁, a₁, fieldsTerm l₁]) = .eq
  · exact ⟨_, opt_map_inter_sameG n₁ n₂ same, Or.inr (Bdd.leaf_iff.mpr lx), fun w => by
      rw [denMF_exact (Or.inr (Bdd.leaf_iff.mpr lx)) (Or.inr (Bdd.leaf_iff.mpr ly)) same, Bool.and_self]⟩
  rcases opt_bdd_seen_map S (.atom "map_intersection") (.tuple #[.integer k₁, a₁, fieldsTerm l₁])
      (.tuple #[.integer k₂, a₂, fieldsTerm l₂]) with seen | ⟨S', ok⟩
  · obtain ⟨r, hr, fr, sr⟩ := inter_plainM (Bdd.leaf_iff.mpr lx) (Bdd.leaf_iff.mpr ly)
    exact ⟨r, by rw [(opt_map_inter_leavesG n₁ n₂ same).1 seen, hr], fr, sr⟩
  rw [(opt_map_inter_leavesG n₁ n₂ same).2 _ ok]
  rcases literal_val ef.mopsE ef.mdopsE ef.msemZ (Kf := K + 1) (show K + 1 + 1 ≤ m by omega) (by omega)
    (opt_ifun ef S') (S := []) rfl g₁ g₂ s₁ s₂ with ⟨tR, l, run, gR, sl, sem⟩ | ⟨disj, run⟩
  · obtain ⟨k, hk, key⟩ := leaf_new_keyM gR (l.map fun e => .tuple #[e.1, e.2])
    have hk' : Elixir.Module.Types.Descr.«bdd_leaf_new/2» tR (fieldsTerm l) =
        .ok (.tuple #[.integer k, tR, fieldsTerm l]) := hk
    refine ⟨.tuple #[.integer k, tR, fieldsTerm l], ?_, leaf_field gR sl key, fun v => ?_⟩
    · simp only [optMapIFun] at run
      simp [Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3», run, hk']
    · apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true, denMF_leaf ef sl gR, denMF_leaf ef s₁ g₁, denMF_leaf ef s₂ g₂]
      exact sem v
  · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
    · simp only [optMapIFun] at run
      simp [Elixir.Module.Types.Descr.«opt_map_leaf_intersection/3», run, Lynx.Except.tryWith,
        Lynx.Exception.classTerm, Lynx.Exception.reason]
    · rw [denMF_bdd Bdd.bot]
      symm
      apply Bool.eq_false_iff.mpr
      intro h
      rw [Bool.and_eq_true, denMF_leaf ef s₁ g₁, denMF_leaf ef s₂ g₂] at h
      exact disj v h

/-- Pushing an open map literal below closed literals keeps exactly the maps of both. -/
theorem push_open_map (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {H : Int} {lo : List (Term × Term)}
    (hL : MLit E (.tuple #[.integer H, .atom "open", fieldsTerm lo])) (hH : 0 ≤ H) {b : Term} (wb : Bdd (MLit E) b) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» (D m) b (.tuple #[.integer H, .atom "open", fieldsTerm lo])
        (.function "Elixir.Module.Types.Descr" "map_closed_subtype_of_open?" 2 #[]) = .ok r ∧
      MField E r ∧ ∀ w, denMF E den r w =
        (denMF E den b w && denMF E den (.tuple #[.integer H, .atom "open", fieldsTerm lo]) w) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  have so : FieldsV E lo := by
    obtain ⟨⟨_, _, l', e, -, sl'⟩, -⟩ := hL
    obtain ⟨-, -, e₂⟩ := tuple3_eq e
    rwa [fieldsTerm_inj e₂]
  obtain ⟨r, run, okr, semr⟩ := open_leaf_ok (Val := fun ρ => ∃ w, ρ = valM E den w) (fun ρ ⟨w, e⟩ => e ▸ valM_resp w)
    (ok := MLit E) (d := D (n + 1)) hL
    (fun k cl h => by
      obtain ⟨l, -, -, -, -, -, kc⟩ := mlit_leaf h
      exact closed_lt_openM (kc rfl) hH cl _)
    (fun k cl h => by
      obtain ⟨⟨k', tag, l, e, -, sl⟩, -⟩ := h
      obtain ⟨-, e₁, e₂⟩ := tuple3_eq e
      subst e₂ e₁
      obtain ⟨c, runc, sound⟩ := cso_val ef (m := n) (by omega) _ l _ (Nat.le_refl _) sl so
      refine ⟨c, by
        rw [Erlang.program.«Elixir.Module.Types.Descr:map_closed_subtype_of_open?/2».pure]
        exact runc, fun cc ρ ⟨w, hw⟩ hρ => ?_⟩
      subst hw
      have lit : MapLitV E (.tuple #[.integer k, .atom "closed", fieldsTerm l]) := MapLitV.atom (Or.inr rfl) sl
      have ns := nsem_lit.mp ((valM_iff ef.mopsE ef.mdopsE ef.semR lit).mp hρ)
      exact (valM_iff ef.mopsE ef.mdopsE ef.semR hL.1).mpr (nsem_lit.mpr ⟨fun s => sound cc s _ (ns s), fun k i => Or.inl rfl⟩))
    (MLit E) b wb (fun t h => h)
  have wr : Bdd (MLit E) r := okr (MLit E) (fun t h => h) hL
  refine ⟨r, run, Or.inr wr, fun w => ?_⟩
  rw [denMF_bdd wr, semr _ ⟨w, rfl⟩, denMF_bdd wb, denMF_bdd (Bdd.leaf_iff.mpr hL), eval_leaf]

/-- Optimized intersections of map types hold the maps of both. -/
theorem opt_map_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {x y : Term} (fx : MField E x)
    (fy : MField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) = .ok r ∧ MField E r ∧
      ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«opt_map_intersection/3»; rfl, fy,
      fun w => by rw [denMF_top]; rfl⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, opt_map_inter_top_eqG (not_top_of_ok wx mlit_not), Or.inr wx, fun w => by rw [denMF_top]; simp⟩
  have nx := not_top_of_ok wx mlit_not
  have ny := not_top_of_ok wy mlit_not
  have plain : Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) =
      Elixir.Module.Types.Descr.«map_intersection/2» x y →
      ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) = .ok r ∧ MField E r ∧
        ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := by
    intro e
    obtain ⟨r, hr, fr, sr⟩ := inter_plainM wx wy
    exact ⟨r, by rw [e, hr], fr, sr⟩
  have plainEq := fun h3 h4 h5 => plain (opt_map_inter_plain_eqG (d := D m) (S := .map S) nx ny h3 h4 h5)
  have xAtom : ∀ {s : String}, x = .atom s → ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) =
      .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ e _ => by cases e) (fun _ _ _ _ _ _ _ e _ => by cases e)
      (fun _ _ _ _ _ _ _ _ e => by cases e)
  have yAtom : ∀ {s : String}, y = .atom s → ∃ r, Elixir.Module.Types.Descr.«opt_map_intersection/3» (D m) x y (.map S) =
      .ok r ∧ MField E r ∧ ∀ w, denMF E den r w = (denMF E den x w && denMF E den y w) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ _ e => by cases e) (fun _ _ _ _ _ _ _ _ e => by cases e)
      (fun _ _ _ _ _ _ _ e _ => by cases e)
  rcases wx.shape with ex | ex | ⟨k₁, a₁, b₁, rfl⟩ | ⟨h₁, lit₁, c₁, u₁, d₁, rfl⟩
  · exact xAtom ex
  · exact xAtom ex
  all_goals rcases wy.shape with ey | ey | ⟨k₂, a₂, b₂, rfl⟩ | ⟨h₂, lit₂, c₂, u₂, d₂, rfl⟩
  all_goals try exact yAtom ey
  -- two leaves
  · exact leaf_inter ef hm ((Bdd.leaf_iff).mp wx) ((Bdd.leaf_iff).mp wy) S
  -- a leaf and a node
  · have lx := (Bdd.leaf_iff).mp wx
    obtain ⟨l, rfl, g, sl, nl, op, -⟩ := mlit_leaf lx
    rcases g with rfl | rfl | ⟨dl, rfl, -⟩
    · have ne : l ≠ [] := fun e => nl ⟨rfl, e⟩
      obtain ⟨r, hr, fr, sr⟩ := push_open_map ef (show K + 1 ≤ m by omega) lx (op rfl) wy
      refine ⟨r, ?_, fr, fun v => by rw [sr v, Bool.and_comm]⟩
      rw [opt_map_inter_push_lG (fun e => ne (fieldsTerm_eq_nil.mp e))]
      exact hr
    all_goals
      exact plainEq (fun _ _ _ _ _ _ _ e => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp [fieldsTerm_ne_atom] at e)
        (fun _ _ _ _ _ _ _ _ e => by simp at e)
  -- a node and a leaf
  · have ly := (Bdd.leaf_iff).mp wy
    obtain ⟨l, rfl, g, sl, nl, op, -⟩ := mlit_leaf ly
    rcases g with rfl | rfl | ⟨dl, rfl, -⟩
    · have ne : l ≠ [] := fun e => nl ⟨rfl, e⟩
      obtain ⟨r, hr, fr, sr⟩ := push_open_map ef (show K + 1 ≤ m by omega) ly (op rfl) wx
      refine ⟨r, ?_, fr, sr⟩
      rw [opt_map_inter_push_rG (fun e => ne (fieldsTerm_eq_nil.mp e))]
      exact hr
    all_goals
      exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
        (fun _ _ _ _ _ _ _ e _ => by simp [fieldsTerm_ne_atom] at e)
  -- two nodes
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun _ _ _ _ _ _ _ e _ => by simp at e)

end Elixir.STTDescrProofsTest.Nest
