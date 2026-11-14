namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The bottom level: top list and map fields, and tuple fields of the expansion literal of the node `t`. -/

theorem sub_term_term (d : Dispatcher) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") (.atom "term") = .ok (.atom "true") := by
  obtain ⟨T, term, -, -, -, staticT⟩ := unfolded_term_fields
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [term, unfold_map, Erlang.erlang.«is_map_key/2», staticT, any_key, Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  simp [Erlang.erlang.«=:=/2»]

theorem empty_term_false (d : Dispatcher) :
    Elixir.Module.Types.Descr.«empty?/1» d (.atom "term") = .ok (boolAtom Bool.false) := by
  unfold Elixir.Module.Types.Descr.«empty?/1»; rfl

theorem topF_lh {name : String} {x : Term} (h : topValue name = some x) : lh x = 0 := by
  rcases top_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [lh, lh_nil_map]

theorem topF_dn {name : String} {x : Term} (hn : name = "list" ∨ name = "map") (h : topValue name = some x)
    (p : Point) : dn name (some x) p = Bool.true := by
  rcases hn with rfl | rfl <;> rcases top_cases h with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
    simp at e <;> simp [dn_list, dn_map, denL_top, denO_top]

/-- Top list and map fields: their operations keep the top value, and they are not empty. -/
theorem topF_of {name : String} (hn : name = "list" ∨ name = "map") {x : Term} (h : FieldOk name x) :
    topValue name = some x := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tx⟩ <;> first | exact tx | (rcases hn with h | h <;> simp at h)

theorem topKind (name : String) (hn : name = "list" ∨ name = "map") {K : Nat} (hK : 1 ≤ K) :
    KindOk K name (FieldOk name) Resp where
  resp := fun _ h => h
  wit := ⟨_, resp_const Bool.true⟩
  top := fun t ht => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    have tv : topValue name = some t := by
      rcases hn with rfl | rfl <;>
        rcases ht with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all [topValue]
    exact ⟨Or.inr (Or.inr ⟨nb, na, tv⟩), topF_lh tv, fun p _ => topF_dn hn tv p⟩
  congr := fun fx fx' _ p _ => by
    rcases fx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tx⟩ <;> try (rcases hn with h | h <;> simp at h)
    rcases fx' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tx'⟩ <;> try (rcases hn with h | h <;> simp at h)
    rw [topF_dn hn tx, topF_dn hn tx']
  union := fun {x y} fx fy => by
    obtain ⟨r, run, fr⟩ := fieldok_union name fx fy
    have tr : topValue name = some r := by
      rcases fr with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tr⟩ <;> first | exact tr | (rcases hn with h | h <;> simp at h)
    refine ⟨r, fun m hm => ?_, fr, fun p _ => by rw [topF_dn hn tr, topF_dn hn (topF_of hn fx)]; rfl,
      by rw [topF_lh tr]; omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact run n
  inter := fun {x y} fx fy => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    obtain ⟨r, run, fr, -, -, kr⟩ := inter_key name x y fx fy
    have k := kr nb na
    have tr := topF_of hn (fr k)
    refine ⟨r, fun m _ => run _, fun _ => ⟨fr k, by rw [topF_lh tr]; omega⟩, fun p _ => ?_⟩
    rw [keptO_true k, topF_dn hn tr, topF_dn hn (topF_of hn fx), topF_dn hn (topF_of hn fy)]
    rfl
  diff := fun {x y} fx fy => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    obtain ⟨r, run, -, -, -, kr⟩ := diff_key name x y fx fy
    have k := kr nb na
    refine ⟨r, fun m _ => run _, fun h => absurd (h.symm.trans k) (by decide), fun p _ => ?_⟩
    rw [keptO_false k, dn_none, topF_dn hn (topF_of hn fy)]
    simp
  opt_union := fun {x y} S {m} fx fy hm => by
    have tx := topF_of hn fx
    have ty := topF_of hn fy
    rw [tx] at ty
    cases ty
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact ⟨x, opt_union_top n tx _, fx, fun p _ => by rw [topF_dn hn tx]; rfl⟩
  opt_inter := fun {x y} S {m} fx fy hm => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    obtain ⟨r, run, fr, -, -, kr⟩ := opt_inter_key m name x y (.map S) fx fy
    have k := kr nb na
    have tr := topF_of hn (fr k)
    refine ⟨r, run, fun _ => fr k, fun p _ => ?_⟩
    rw [keptO_true k, topF_dn hn tr, topF_dn hn (topF_of hn fx), topF_dn hn (topF_of hn fy)]
    rfl
  opt_diff := fun {x y} S {m} fx fy hm => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    have tx := topF_of hn fx
    have ty := topF_of hn fy
    rw [tx] at ty
    cases ty
    obtain ⟨r, run, -, -, -, kr⟩ := diff_key name x x fx fx
    have k := kr nb na
    refine ⟨r, by rw [opt_diff_top _ tx, run], fun h => absurd (h.symm.trans k) (by decide), fun p _ => ?_⟩
    rw [keptO_false k, dn_none, topF_dn hn tx]
    rfl
  empty := fun {x} S fx => by
    have tx := topF_of hn fx
    obtain ⟨b, run⟩ : ∃ b, ∀ d, Elixir.Module.Types.Descr.«empty_key?/3» d (.atom name) x (.map S) = .ok (boolAtom b) := by
      rcases hn with rfl | rfl <;> rcases top_cases tx with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp at e
      · refine ⟨Bool.false, fun d => ?_⟩
        simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using list_top_nonempty d (.map S)
      · obtain ⟨b, h⟩ := map_top_bool S
        exact ⟨b, fun d => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h d⟩
    refine ⟨b, fun m _ => run _, fun N _ hS => ?_⟩
    have e : b = Bool.false := by
      rcases hn with rfl | rfl <;> rcases top_cases tx with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp at e
      · have r₀ := list_top_nonempty (D 0) (.map S)
        have r₁ := run (D 0)
        simp only [Elixir.Module.Types.Descr.«empty_key?/3»] at r₁
        rw [r₀] at r₁
        cases b <;> simp_all [boolAtom]
      · have r₀ := map_top_nonempty (D 0) (safeF_of hS)
        have r₁ := run (D 0)
        simp only [Elixir.Module.Types.Descr.«empty_key?/3»] at r₁
        rw [r₀] at r₁
        cases b <;> simp_all [boolAtom]
    subst e
    refine ⟨fun h => by simp at h, fun h => ?_⟩
    have := h (0, .nil, fun _ => Bool.true) (resp_const _)
    rw [topF_dn hn tx] at this
    cases this

/-! Tuple fields of the bottom level: BDDs of the expansion literal of `t`. -/

section
variable {t : Term}

theorem pure_diff_sem {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && !denO y ρ) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, Or.inr Bdd.bot,
      fun ρ _ => by simp [denO, isOpenTop, eval]⟩
  have ny := not_top_of_ok wy pureLit_not
  have special : ¬∃ k, y = .tuple #[k, .atom "closed", .nil] := by
    rintro ⟨k, rfl⟩
    unfold Bdd at wy
    split at wy <;> simp_all [PureLit, litN, Term.list]
    obtain ⟨e, -, -, h⟩ := wy
    cases h
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun ρ _ => by simp [denO, isOpenTop, eval]⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_top]
    · refine ⟨_, ?_, Or.inl ⟨kt, rfl⟩, fun ρ _ => by simp [denO, isOpenTop, eval]⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    all_goals
      obtain ⟨w, run, keep, sem⟩ := neg_ok wy
      refine ⟨w, ?_, Or.inr (keep _ wy), fun ρ r => ?_⟩
      · rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
      · rw [denO_top, denO_bdd pureLit_not (keep _ wy), denO_bdd pureLit_not wy, sem ρ r]; rfl
  · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
    refine ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx pureLit_not) ny (fun ⟨_, h⟩ => special h), run],
      Or.inr (keep _ wx wy), fun ρ r => ?_⟩
    rw [denO_bdd pureLit_not (keep _ wx wy), denO_bdd pureLit_not wx, denO_bdd pureLit_not wy, sem ρ r]

end

section
variable {t : Term}

/-- Optimized intersections of pure tuple fields are their plain ones. -/
theorem pure_opt_inter {d : Dispatcher} {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) (S : Term) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»; rfl, fy, fun ρ _ => by rw [denO_top]; rfl⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, opt_tuple_inter_top_eq (not_top_of_ok wx pureLit_not), Or.inr wx, fun ρ _ => by rw [denO_top]; simp⟩
  have nx := not_top_of_ok wx pureLit_not
  have ny := not_top_of_ok wy pureLit_not
  have plain : Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S =
      Elixir.Module.Types.Descr.«tuple_intersection/2» x y →
      ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧ OField (PureLit t) w ∧
        ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := by
    intro e
    obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [e, tuple_intersection_bdd nx ny, hr], Or.inr wr, fun ρ hρ => ?_⟩
    rw [denO_bdd pureLit_not wr, denO_bdd pureLit_not wx, denO_bdd pureLit_not wy, semr _ hρ]
  have plainEq := fun h3 h4 h5 => plain (opt_tuple_inter_plain_eq (d := d) (S := S) nx ny h3 h4 h5)
  have closed : ∀ {k fo}, PureLit t (.tuple #[k, .atom "open", fo]) → False := by
    rintro k fo ⟨e, -, h⟩
    simp [litN] at h
  have xAtom : ∀ {s : String}, x = .atom s → ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧
      OField (PureLit t) w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ e _ => by cases e) (fun _ _ _ _ _ _ _ e _ => by cases e)
      (fun _ _ _ _ _ _ _ _ e => by cases e)
  have yAtom : ∀ {s : String}, y = .atom s → ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧
      OField (PureLit t) w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ _ e => by cases e) (fun _ _ _ _ _ _ _ _ e => by cases e)
      (fun _ _ _ _ _ _ _ e _ => by cases e)
  rcases wx.shape with ex | ex | ⟨k₁, a₁, b₁, rfl⟩ | ⟨h₁, lit₁, c₁, u₁, d₁, rfl⟩
  · exact xAtom ex
  · exact xAtom ex
  all_goals rcases wy.shape with ey | ey | ⟨k₂, a₂, b₂, rfl⟩ | ⟨h₂, lit₂, c₂, u₂, d₂, rfl⟩
  all_goals try exact yAtom ey
  · have same := pureLit_exact (Bdd.leaf_iff.mp wx) (Bdd.leaf_iff.mp wy)
    exact ⟨_, opt_tuple_inter_same (pureLit_not _ (Bdd.leaf_iff.mp wx)) same, Or.inr wx,
      fun ρ hρ => by rw [denO_congr pureLit_not (Or.inr wy) (Or.inr wx) (compare_eq_of_compareExact_eq _ _ same) hρ,
        Bool.and_self]⟩
  · exact plainEq (fun _ _ _ _ _ _ _ e => by simp at e) (fun k fo _ _ _ _ _ e _ => closed (e ▸ Bdd.leaf_iff.mp wx))
      (fun _ _ _ _ _ _ _ e => by simp at e)
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun k fo _ _ _ _ _ e _ => closed (e ▸ Bdd.leaf_iff.mp wy))
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun _ _ _ _ _ _ _ e _ => by simp at e)

end

section
variable {t : Term}

/-- Expansions of accepted nodes meet: both hold nil. -/
theorem disj_expN {e e' : Term} (he : IsT t e) (he' : IsT t e') {m : Nat} (hm : 8 ≤ m) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D m) (expN e (keyOf t)) (expN e' (keyOf t)) = .ok (.atom "false") := by
  obtain ⟨s, run⟩ := (pure_sub_disj t).2 (Or.inr ⟨_, rfl, expN_pure he⟩) (Or.inr ⟨_, rfl, expN_pure he'⟩)
  have r := run m (by omega)
  cases s
  · simpa [boolAtom, expN] using r
  exfalso
  have pA := expN_pure he
  have pB := expN_pure he'
  have calls : ∀ {X Y : List (Term × Term)}, PureMap t X → PureMap t Y → ∀ e ∈ mapEntries X,
      ∀ y d', 2 ≤ d' → mapLookup Y e.1 = some y → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
          ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/2» (D d') e.1 w = .ok (boolAtom b)) := by
    intro X Y sX sY x mx y d' hd hy
    have hx := mapLookup_of_mem_mapEntries mx
    obtain ⟨name, key⟩ := sX.atomKey hx
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k⟩ := interP t name x.2 y (sX.fields name x.2 hx) (sY.fields name y hy)
    refine ⟨w, run _, fun kw => ?_⟩
    by_cases nt : name = "tuple"
    · subst nt
      obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple (k kw)) []
      exact ⟨b, by simpa [Elixir.Module.Types.Descr.«empty_key?/2», Elixir.Module.Types.Descr.«empty_key?/3»] using hb d' hd⟩
    · have h := fieldok_empty (D d') name (fieldP_other (k kw) nt)
      exact ⟨Bool.false, by simpa [Elixir.Module.Types.Descr.«empty_key?/2»] using h⟩
  -- the walk finds the atom field, whose intersection holds nil
  have stA := pA.static
  have stB := pB.static
  have hit : ∀ {X Y : List (Term × Term)}, PureMap t X → PureMap t Y →
      mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) →
      mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) →
      (∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∃ d', 2 ≤ d' ∧ ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/2» (D d') e.1 w = .ok (.atom "true"))) →
      False := by
    intro X Y sX sY hX hY walk
    obtain ⟨x, mx, qx, -⟩ : ∃ x ∈ mapEntries X, compareExact (fuel (.atom "atom") x.1) (.atom "atom") x.1 = .eq ∧ True := by
      have : (mapLookup (mapEntries X) (.atom "atom")).isSome := by rw [mapLookup_mapEntries, hX]; rfl
      obtain ⟨x, mx, qx⟩ := (mapLookup_isSome _ _).mp this
      exact ⟨x, mx, qx, trivial⟩
    have key : x.1 = .atom "atom" := ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qx))
    have hx := mapLookup_of_mem_mapEntries mx
    rw [key, hX] at hx
    obtain ⟨d', -, w, run, out⟩ := walk x mx _ (by rw [key]; exact hY)
    rw [key] at run out
    have hx' : x.2 = .tuple #[.atom "union", .map [(.atom "nil", .nil)]] := (Option.some.inj hx).symm
    rw [hx'] at run
    have fa : FieldOk "atom" (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) :=
      fieldP_other (sX.fields "atom" _ hX) (by decide)
    obtain ⟨r₀, rr, -, -, am, -⟩ := inter_key "atom" _ _ fa fa
    have e₀ : r₀ = w := by have := (rr (D d')).symm.trans run; simpa using this
    subst e₀
    have kr : kept (.atom "atom", r₀) = Bool.true := by
      have := am rfl (.atom "nil")
      cases k : kept (.atom "atom", r₀)
      · simp [k, amemV, mapLookup] at this
      · rfl
    rcases out with k | em
    · rw [k] at kr; cases kr
    · simp [Elixir.Module.Types.Descr.«empty_key?/2», Elixir.Module.Types.Descr.«empty_key?/3»] at em
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (expN e (keyOf t)) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (expN e' (keyOf t)) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  simp only [expN] at hsa hsb
  have ue := upper_expN (D m) e (keyOf t)
  have ue' := upper_expN (D m) e' (keyOf t)
  simp only [expN] at ue ue'
  have h := r
  simp only at h
  unfold Elixir.Module.Types.Descr.«disjoint?/2» at h
  simp [getMapKeys_single, mapLookup, boolAtom] at h
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2» at h
  have hA : mapLookup [(.atom "tuple", litN e (keyOf t)), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]
      (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) := by simp [mapLookup]
  have hB : mapLookup [(.atom "tuple", litN e' (keyOf t)), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]
      (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) := by simp [mapLookup]
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen 2 _ (mapEntries _) (calls pB pA) m
      (by have := entries_le_six pB.keys; omega) (not_true (by rw [bind_assoc]; exact h))
    exact hit pB pA hB hA walk
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen 2 _ (mapEntries _) (calls pA pB) m
      (by have := entries_le_six pA.keys; omega) (not_true (by rw [bind_assoc]; exact h))
    exact hit pA pB hA hB walk
end

section
variable {t : Term}

/-- `opt_tuple_leaf_difference/3` finds expansion literals in each other. -/
theorem pure_cmp {n : Nat} (hn : 8 ≤ n) (a₁ a₂ type : Term) (h₁ : PureLit t a₁) (h₂ : PureLit t a₂) :
    ∃ res, (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "opt_tuple_leaf_difference" 3 #[])
      #[a₁, a₂, type] = .ok res ∧ CmpOk Resp (PureLit t) a₁ a₂ type res := by
  obtain ⟨e₁, he₁, rfl⟩ := h₁
  obtain ⟨e₂, he₂, rfl⟩ := h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:opt_tuple_leaf_difference/3».pure]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have dtt : Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) (.atom "term") (.atom "term") = .ok (.atom "false") := by
    rw [disj_term_l, empty_term_false]; rfl
  have stt := sub_term_term (D (m + 1))
  have dee : Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) e₁ e₂ = .ok (.atom "false") := by
    rw [disj_node_l he₁.node m (expand_isT he₁ m) _ (node_ne_term he₂) (fun X h => by obtain ⟨S, rfl, -⟩ := he₂.node; cases h),
      disj_node_r he₂.node m (expand_isT he₂ m) _ (expN_ne_term _ _) (fun X h => by simp [expN] at h; subst h; simp [mapLookup])]
    exact disj_expN he₁ he₂ (by omega)
  obtain ⟨s, hs⟩ := (pure_sub_disj t).1 (Or.inr ⟨_, rfl, expN_pure he₁⟩) (Or.inr ⟨_, rfl, expN_pure he₂⟩)
  have see : Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) e₁ e₂ = .ok (boolAtom s) := by
    rw [sub_node_l he₁.node m (expand_isT he₁ m), sub_node_r he₂.node m (expand_isT he₂ m)]
    exact hs _ (by omega)
  refine ⟨if s then .atom "subtype" else .atom "none", ?_, ?_⟩
  · simp only [litN, Term.list]
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp [Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«/=/2», Erlang.erlang.«==/2»]
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp [dtt, stt, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp [dee, see, Lynx.Except.guard, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
    cases s
    · simp [boolAtom]
    · simp [boolAtom]
      rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
      simp [isMember]
  · cases s
    · exact Or.inr (Or.inr (Or.inr rfl))
    · refine Or.inr (Or.inl ⟨rfl, fun ρ hρ h => ?_⟩)
      rw [← hρ _ _ (compare_eq_of_compareExact_eq _ _ (pureLit_exact ⟨e₂, he₂, rfl⟩ ⟨e₁, he₁, rfl⟩))]
      exact h

/-- Optimized differences of pure tuple fields. -/
theorem pure_opt_diff {n : Nat} (hn : 8 ≤ n) {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_difference/2» (D (n + 1)) x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && !denO y ρ) := by
  obtain ⟨w, run, fw, sem⟩ := pure_diff_sem fx fy
  rcases opt_tuple_split (D (n + 1)) x y with e | ⟨e, eb, ny, nx⟩ | ⟨k, a, b, rfl, same, e⟩
  · exact ⟨w, by rw [e, run], fw, sem⟩
  rotate_left
  · refine ⟨_, e, Or.inr Bdd.bot, fun ρ hρ => ?_⟩
    rw [denO_congr pureLit_not fy fx (compare_eq_of_compareExact_eq _ _ same) hρ,
      show denO (.atom "bdd_bot") ρ = Bool.false by simp [denO, isOpenTop]]
    cases denO (.tuple #[k, a, b]) ρ <;> rfl
  rw [e]
  have wy : Bdd (PureLit t) y := by
    rcases fy with ⟨k, rfl⟩ | wy
    · exact absurd rfl (ny _)
    · exact wy
  rcases fx with ⟨k, rfl⟩ | wx
  · rcases nx with nx | nx
    · exact absurd rfl (nx _)
    have wx : Bdd (fun l => l = .tuple #[.integer k, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) :=
      Bdd.leaf_iff.mpr rfl
    rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
  obtain ⟨r, hr, okr, semr⟩ := diff3_ok (Val := Resp) (fun _ h => h)
    (fun a₁ a₂ type _ h₁ h₂ => pure_cmp hn a₁ a₂ type h₁ h₂) _ y wy (fun _ h => h) x wx
  refine ⟨r, hr, Or.inr okr, fun ρ hρ => ?_⟩
  rw [denO_bdd pureLit_not okr, denO_bdd pureLit_not wx, denO_bdd pureLit_not wy, semr _ hρ]

/-- Expansion literals fuse into themselves. -/
theorem pure_fuse_leaf (d : Dispatcher) {e e' : Term} (he : IsT t e) (he' : IsT t e') :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» d (litN e (keyOf t)) (litN e' (keyOf t)) = .ok (litN e (keyOf t)) := by
  have ee := isT_exact he' he
  have leaf := leaf_isT he
  simp only [litN, Term.list] at leaf ⊢
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
  simp [Erlang.erlang.«=:=/2», Erlang.erlang.«length/1», Erlang.erlang.«==/2», Erlang.erlang.«and/2»,
    Term.true]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
  simp [Erlang.erlang.«=:=/2»]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
  simp [Erlang.erlang.«=:=/2», ee]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
  simp [Erlang.lists.«reverse/1», leaf]
  done

theorem pure_union {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) :=
  open_union_spec pureLit_not _ tuple_union_shape.1 tuple_union_shape.2.1 tuple_union_shape.2.2 fx fy

theorem chain_atom (d : Dispatcher) (s : String) (leaf z : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» d (.atom s) leaf z = .ok (.atom "nil") := by
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
  split <;> first | rfl | simp_all

theorem fuse_leaf_top (d : Dispatcher) (e : Term) (k k' : Int) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» d (litN e k) (.tuple #[.integer k', .atom "open", .nil]) =
      .ok (.atom "nil") := by
  simp only [litN, Term.list]
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
  simp [Erlang.erlang.«=:=/2», Erlang.erlang.«and/2», Term.false,
    Erlang.erlang.«length/1», Erlang.erlang.«==/2»]

theorem hρ_same {e e' : Term} (he : IsT t e) (he' : IsT t e') (ρ : Term → Bool) (hρ : Resp ρ) :
    ρ (litN e' (keyOf t)) = ρ (litN e (keyOf t)) :=
  hρ _ _ (compare_eq_of_compareExact_eq _ _ (pureLit_exact ⟨e, he, rfl⟩ ⟨e', he', rfl⟩))

/-- Adding a leaf to a node of expansion literals. -/
theorem pure_union_leaf (m : Nat) {j : Int} {e₀ : Term} (h₀ : IsT t e₀) (c u d : Bool)
    (fb : OField (PureLit t) (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d])) {leaf : Term}
    (fl : OField (PureLit t) leaf) (lf : (∃ k, leaf = .tuple #[.integer k, .atom "open", .nil]) ∨ PureLit t leaf) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m)
      (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) leaf = .ok r ∧ OField (PureLit t) r ∧
      ∀ ρ, Resp ρ → denO r ρ = (denO (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) ρ || denO leaf ρ) := by
  obtain ⟨w, run, fw, sem⟩ := pure_union fb fl
  have plain : Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m)
      (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) leaf (.integer 64) = .ok (.atom "nil") →
      ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m)
        (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) leaf = .ok r ∧ OField (PureLit t) r ∧
        ∀ ρ, Resp ρ → denO r ρ = (denO (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) ρ || denO leaf ρ) := by
    intro ch
    refine ⟨w, ?_, fw, sem⟩
    rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
    simp [ch, run]
  by_cases shape : c = Bool.true ∧ d = Bool.false
  · obtain ⟨rfl, rfl⟩ := shape
    rcases lf with ⟨k, rfl⟩ | ⟨e', he', rfl⟩
    · apply plain
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
      cases u <;> simp [bt, fuse_leaf_top, isMember, chain_atom]
    · have fl' : Bdd (PureLit t) (litN e₀ (keyOf t)) := Bdd.leaf_iff.mpr ⟨e₀, h₀, rfl⟩
      have fl'' : Bdd (PureLit t) (litN e' (keyOf t)) := Bdd.leaf_iff.mpr ⟨e', he', rfl⟩
      have wb : Bdd (PureLit t) (.tuple #[.integer j, litN e₀ (keyOf t), bt Bool.true, bt u, bt Bool.false]) := by
        rcases fb with ⟨k, h⟩ | w
        · simp at h
        · exact w
      have same := hρ_same (t := t) h₀ he'
      have ch : ∀ uu : Term, Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m)
          (.tuple #[.integer j, litN e₀ (keyOf t), bt Bool.true, uu, bt Bool.false]) (litN e' (keyOf t)) (.integer 64) =
          .ok (.tuple #[litN e₀ (keyOf t), uu]) := by
        intro uu
        rw [show bt Bool.true = .atom "bdd_top" from rfl, show bt Bool.false = .atom "bdd_bot" from rfl,
          Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        simp only [pure_fuse_leaf (D m) h₀ he']
        simp [isMember, litN, Term.list]
      cases u
      · refine ⟨_, ?_, Or.inr fl', fun ρ hρ => ?_⟩
        · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def, ch]
          rfl
        · rw [denO_bdd pureLit_not fl', denO_bdd pureLit_not fl'', denO_bdd pureLit_not wb]
          have s' := same ρ hρ
          simp only [litN, Term.list] at s' ⊢
          simp [eval, bt, s']
      · obtain ⟨w', run', fw', sem'⟩ := pure_union (Or.inr (Bdd.top (ok := PureLit t))) (Or.inr fl')
        refine ⟨w', ?_, fw', fun ρ hρ => ?_⟩
        · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def, ch]
          simp only [bt]
          simp
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
          simp [chain_atom, run']
        · rw [sem' ρ hρ, denO_bdd pureLit_not (Bdd.top (ok := PureLit t)), denO_bdd pureLit_not wb]
          simp [eval, bt]
  · apply plain
    rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
    cases c <;> cases d <;> simp_all [bt]
    all_goals done

theorem via_pure_union {m : Nat} {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y)
    (e : Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = Elixir.Module.Types.Descr.«tuple_union/2» x y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) := by
  obtain ⟨w, run, fw, sem⟩ := pure_union fx fy
  exact ⟨w, by rw [e, run], fw, sem⟩

/-- Optimized unions of pure tuple fields. -/
theorem pure_opt_union (m : Nat) {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) := by
  have fx' := fx
  have fy' := fy
  rcases pure_cases fx with ⟨k₁, rfl⟩ | rfl | rfl | ⟨e₁, h₁, rfl⟩ | ⟨j₁, e₁, c₁, u₁, d₁, h₁, rfl⟩ <;>
    rcases pure_cases fy with ⟨k₂, rfl⟩ | rfl | rfl | ⟨e₂, h₂, rfl⟩ | ⟨j₂, e₂, c₂, u₂, d₂, h₂, rfl⟩
  all_goals first
    | exact via_pure_union fx' fy' (by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; rfl)
    | (apply via_pure_union fx' fy'
       unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
       simp only [leaf_guard, atom_ne3, node_ne3, ite_false, litN, Term.list]
       done)
    | skip
  -- two top leaves
  · by_cases same : compareExact (fuel (.tuple #[.integer k₂, .atom "open", .nil]) (.tuple #[.integer k₁, .atom "open", .nil])) (.tuple #[.integer k₂, .atom "open", .nil]) (.tuple #[.integer k₁, .atom "open", .nil]) = .eq
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp only [leaf_guard, ite_eq_left same]; rfl,
        fx', fun ρ _ => by simp [denO_top]⟩
    have st := strategy_start (D m) "open" "open" (Or.inl rfl) (Or.inl rfl) [] []
    simp only [Term.list, List.length_nil, and_self, ite_true] at st
    rw [show Term.nil = Term.list [] from rfl, index_nil_left] at st
    refine ⟨_, ?_, fy', fun ρ _ => by simp [denO_top]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2», same, st, endSt]
  -- the top leaf and a literal
  · have same : ¬compareExact (fuel (litN e₂ (keyOf t)) (.tuple #[.integer k₁, .atom "open", .nil])) (litN e₂ (keyOf t)) (.tuple #[.integer k₁, .atom "open", .nil]) = .eq := by
      simp [litN, Term.list, compareExact_tuple, List.compareLex_cons_cons]
    have st := strategy_start (D m) "open" "closed" (Or.inl rfl) (Or.inr rfl) [] [.atom "term", e₂]
    simp only [List.length_nil, List.length_cons, String.reduceEq, false_and, ite_false, true_and] at st
    rw [index_nil_left] at st
    refine ⟨_, ?_, fx', fun ρ _ => by simp [denO_top]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2», litN, Term.list, compareExact_tuple, List.compareLex_cons_cons] at st ⊢
    simp [st, endSt]
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₂ c₂ u₂ d₂ fy' fx' (Or.inl ⟨k₁, rfl⟩)
    refine ⟨r, ?_, fr, fun ρ hρ => by rw [sr ρ hρ, Bool.or_comm]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [leaf_guard, node_ne3, ite_false]
    exact hr
  · have same : ¬compareExact (fuel (.tuple #[.integer k₂, .atom "open", .nil]) (litN e₁ (keyOf t))) (.tuple #[.integer k₂, .atom "open", .nil]) (litN e₁ (keyOf t)) = .eq := by
      simp [litN, Term.list, compareExact_tuple, List.compareLex_cons_cons]
    have st := strategy_start (D m) "closed" "open" (Or.inr rfl) (Or.inl rfl) [.atom "term", e₁] []
    simp only [List.length_nil, List.length_cons, String.reduceEq, false_and, ite_false, true_and] at st
    rw [index_nil_right] at st
    refine ⟨_, ?_, fy', fun ρ _ => by simp [denO_top]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2», litN, Term.list, compareExact_tuple, List.compareLex_cons_cons] at st ⊢
    simp [st, endSt]
  · have same := pureLit_exact ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
    refine ⟨_, ?_, fx', fun ρ hρ => by rw [denO_congr pureLit_not fy' fx' (compare_eq_of_compareExact_eq _ _ same) hρ,
      Bool.or_self]⟩
    have same' := same
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [litN, Term.list] at same' ⊢
    simp only [leaf_guard, ite_eq_left same']
    rfl
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₂ c₂ u₂ d₂ fy' fx' (Or.inr ⟨e₁, h₁, rfl⟩)
    refine ⟨r, ?_, fr, fun ρ hρ => by rw [sr ρ hρ, Bool.or_comm]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [leaf_guard, node_ne3, ite_false, litN, Term.list]
    exact hr
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₁ c₁ u₁ d₁ fx' fy' (Or.inl ⟨k₂, rfl⟩)
    refine ⟨r, ?_, fr, sr⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only []
    exact hr
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₁ c₁ u₁ d₁ fx' fy' (Or.inr ⟨e₂, h₂, rfl⟩)
    refine ⟨r, ?_, fr, sr⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [litN, Term.list]
    exact hr

theorem pure_lh_bound {x y w : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) (fw : OField (PureLit t) w)
    (tops : (∃ k, x = .tuple #[.integer k, .atom "open", .nil]) → (∃ k, y = .tuple #[.integer k, .atom "open", .nil]) →
      lh w = 0) : lh w ≤ max (lh x) (lh y) := by
  by_cases tx : ∃ k, x = .tuple #[.integer k, .atom "open", .nil]
  · by_cases ty : ∃ k, y = .tuple #[.integer k, .atom "open", .nil]
    · rw [tops tx ty]; omega
    · have := pure_one fy fun k h => ty ⟨k, h⟩
      have := pure_le fw
      omega
  · have := pure_one fx fun k h => tx ⟨k, h⟩
    have := pure_le fw
    omega

theorem pure_nz {w : Term} (fw : OField (PureLit t) w) : w ≠ .integer 0 := by
  rcases fw with ⟨k, rfl⟩ | ww
  · simp
  · exact bdd_ne_zero ww

/-- Tuple fields of expansion literals of the node `t`, at the bottom level. -/
theorem pureKind {K : Nat} (hK : 10 ≤ K) : KindOk K "tuple" (OField (PureLit t)) Resp where
  resp := fun _ h => h
  wit := ⟨_, resp_const Bool.true⟩
  top := fun t' ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ | ⟨h, _⟩ <;> try simp at h
    exact ⟨Or.inl ⟨_, rfl⟩, lh_top_leaf _, fun p _ => by rw [dn_tuple, denO_top]⟩
  congr := fun fx fx' e p hp => by
    rw [dn_tuple, dn_tuple]
    exact denO_congr pureLit_not fx fx' e hp
  union := fun {x y} fx fy => by
    obtain ⟨w, run, fw, sem⟩ := pure_union fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], fw,
      fun p hp => by rw [dn_tuple, dn_tuple, dn_tuple, sem _ hp], pure_lh_bound fx fy fw fun ⟨k, ex⟩ _ => ?_⟩
    subst ex
    rw [tuple_union_shape.1] at run
    cases run
    exact lh_top_leaf _
  inter := fun {x y} fx fy => by
    obtain ⟨w, run, k, d⟩ := open_inter_spec pureLit_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
      tuple_inter_shape.2.2 (.atom "tuple") fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run],
      fun kw => ⟨(k kw).1, pure_lh_bound fx fy (k kw).1 fun ⟨k₁, ex⟩ ⟨k₂, ey⟩ => ?_⟩, fun p hp => ?_⟩
    · subst ex ey
      rw [tuple_inter_shape.1] at run
      cases run
      exact lh_top_leaf _
    · cases kk : kept (.atom "tuple", w)
      · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, d kk _ hp]
      · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, (k kk).2 _ hp]
  diff := fun {x y} fx fy => by
    obtain ⟨w, run, fw, sem⟩ := pure_diff_sem fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run],
      fun kw => ⟨fw, pure_lh_bound fx fy fw fun ⟨k₁, ex⟩ ⟨k₂, ey⟩ => ?_⟩, fun p hp => ?_⟩
    · subst ex ey
      have : w = .atom "bdd_bot" := by
        unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
        simp at run
        exact run.symm
      subst this
      simp [kept] at kw
    · cases kk : kept (.atom "tuple", w)
      · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, ← sem _ hp,
          dropped_bdd (by rw [kept_name]; exact kk) (pure_nz fw)]
        simp [denO, isOpenTop]
      · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, sem _ hp]
  opt_union := fun {x y} S {m} fx fy hm => by
    obtain ⟨w, run, fw, sem⟩ := pure_opt_union m fx fy
    exact ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_union/4»] using run, fw,
      fun p hp => by rw [dn_tuple, dn_tuple, dn_tuple, sem _ hp]⟩
  opt_inter := fun {x y} S {m} fx fy hm => by
    obtain ⟨w, run, fw, sem⟩ := pure_opt_inter (d := D m) fx fy (.map S)
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_intersection/4»] using run, fun _ => fw, fun p hp => ?_⟩
    cases kk : kept (.atom "tuple", w)
    · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, ← sem _ hp,
        dropped_bdd (by rw [kept_name]; exact kk) (pure_nz fw)]
      simp [denO, isOpenTop]
    · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, sem _ hp]
  opt_diff := fun {x y} S {m} fx fy hm => by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    obtain ⟨w, run, fw, sem⟩ := pure_opt_diff (n := n) (by omega) fx fy
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, fun _ => fw, fun p hp => ?_⟩
    cases kk : kept (.atom "tuple", w)
    · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, ← sem _ hp,
        dropped_bdd (by rw [kept_name]; exact kk) (pure_nz fw)]
      simp [denO, isOpenTop]
    · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, sem _ hp]
  empty := fun {x} S fx => by
    obtain ⟨b, run⟩ := pure_tuple_empty fx S
    refine ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m (by omega),
      fun N hx hS => ?_⟩
    have v := pure_empty_val fx (not_seen hS hx "tuple") (safeN_noid hS _) (m := 2) (by omega)
    rw [run 2 (by omega)] at v
    have hb : b = (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)) := by
      cases b <;> cases h : (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)) <;> simp_all [boolAtom]
    subst hb
    constructor
    · intro h p hp
      rw [dn_tuple]
      obtain ⟨c, hc⟩ := pure_val fx hp
      rw [hc]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      cases c
      · exact h.2
      · exact h.1
    · intro h
      have h₁ := h (0, .nil, fun _ => Bool.true) (resp_const _)
      have h₂ := h (0, .nil, fun _ => Bool.false) (resp_const _)
      rw [dn_tuple] at h₁ h₂
      simp [h₁, h₂]

end

/-- The kinds of the bottom level. -/
theorem kinds0 (t : Term) {K : Nat} (hK : 10 ≤ K) :
    Kinds K (OField (PureLit t)) (FieldOk "list") (FieldOk "map") Resp Resp Resp :=
  ⟨pureKind hK, topKind "list" (Or.inl rfl) (by omega), topKind "map" (Or.inr rfl) (by omega)⟩

end Elixir.STTDescrProofsTest.Nest
