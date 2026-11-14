namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Subtyping is an order, and disjointness is exact, on types whose function types are arrows. -/

section
variable {L : Level}

/-- The fields of a gradual map other than its dynamic part are those of its lower bound. -/
theorem gc_fields {X : List (Term × Term)} (hX : GC L (.map X)) {name : String} (h : name ≠ "dynamic") {x : Term}
    (hx : mapLookup X (.atom name) = some x) : FC L name x := by
  have t := hX.low_tc
  rcases t with e | ⟨X', e, sX⟩
  · simp [lower] at e
  · simp only [lower, Term.map.injEq] at e
    subst e
    exact sX.fields name x (by rw [lookup_rmDyn_name X h]; exact hx)

/-- Gradual types equal by comparison hold the same points, at both bounds. -/
theorem gc_congr {a b : Term} (ha : GC L a) (hb : GC L b) (e : Term.compare (Term.fuel a b) a b = .eq) (v : TP L) :
    (denD a v ↔ denD b v) ∧ (denD (upper a) v ↔ denD (upper b) v) := by
  rcases ha.shape with rfl | ⟨X, rfl⟩ <;> rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · have fields : denD (.map X) v ↔ denD (.map Y) v := by
      rw [denD_map, denD_map]
      have ne := names_ne_dyn v.2.1
      have rel := lookup_rel_cmp e (.atom v.1.1)
      cases hx : mapLookup X (.atom v.1.1) <;> cases hy : mapLookup Y (.atom v.1.1) <;> rw [hx, hy] at rel <;>
        cases rel
      rename_i x y cmp
      rw [fieldC_congr (tks L) (tfc L) (gc_fields ha ne hx) (gc_fields hb ne hy) cmp v.1.2 v.2.2]
    refine ⟨fields, ?_⟩
    have rel := lookup_rel_cmp e (.atom "dynamic")
    cases hx : mapLookup X (.atom "dynamic") <;> cases hy : mapLookup Y (.atom "dynamic") <;> rw [hx, hy] at rel <;>
      cases rel
    · simp only [upper, hx, hy, Option.getD_none]
      exact fields
    rename_i x y cmp
    have tx := ha.up_tc; have ty := hb.up_tc
    rw [upper_dyn hx] at tx ⊢; rw [upper_dyn hy] at ty ⊢
    exact tc_congr tx ty cmp v

end

section
variable {t : Term} {n : Nat}

/-- Points of the next level, whose function fields hold sets of functions. -/
abbrev PN (t : Term) (n : Nat) : Type :=
  PtD (level t n).E (level t n).den (level t n).tl (FVal (level t n).E (level t n).den)

/-- A point of the next level, as a point of the top-level types. -/
def toTPN (v : PN t n) : TP (level t n) := v

theorem denD_toTPN (a : Term) (v : PN t n) : denD a (toTPN v) ↔ denD a v := Iff.rfl

/-- Inclusion of types over the points of the next level. -/
def SubN (t : Term) (n : Nat) (a b : Term) : Prop := ∀ v : PN t n, denD a v → denD b v

theorem ef_next (t : Term) (n : Nat) : EF (level t n).nd (DE (level t n).E) (PN t n) denD tlD ((level t n).K + 23) :=
  ef_step (level t n).ef (level t n).none

/-- Subtyping of types whose function types are arrows is exact. -/
theorem next_sub {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom (bp (SubN t n a b))) := by
  have ef3 := ef_next t n
  obtain ⟨s, rs, ss⟩ := ef3.sub ha hb
  by_cases h : SubN t n a b
  · rw [ef3.subc ha hb h m hm, bp_true.mpr h]; rfl
  · rw [rs m hm, bp_false.mpr h]
    cases s
    · rfl
    · exact absurd (ss rfl) h

/-- The subtraction check of `subtype?/2` is exact on types whose function types are arrows. -/
theorem next_esub {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«empty_difference_subtype?/3» (D m) a b (.map []) =
      .ok (boolAtom (bp (SubN t n a b))) := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · have e := compare_eq_of_compareExact_eq _ _ same
    have incl : ∀ v : TP (level t n), denD a v → denD b v := fun v h =>
      (tc_congr (de_tc hb) (de_tc ha) e v).mpr h
    rw [esub_complete (de_tc ha) (de_tc hb) (by omega) incl, bp_true.mpr (show SubN t n a b from fun v h => incl (toTPN v) h)]
    rfl
  · have run := sstatic_sub (de_tc ha) (de_tc hb) (m := m) (by omega)
    unfold Elixir.Module.Types.Descr.«subtype_static?/2» at run
    simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»] at run
    rw [run, next_sub ha hb hm]

/-- The lower bound of a gradual type is included in its upper bound. -/
theorem gc_inv_n {a : Term} (ga : GC (level t n) a) : SubN t n (lower a) (upper a) := fun v h =>
  ga.inv (toTPN v) ((denD_lower a (toTPN v)).mp h)

theorem bp_and (p q : Prop) : (bp p && bp q) = bp (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Gradual subtyping on maps compares both bounds exactly. -/
theorem gd_sub_maps {X Y : List (Term × Term)} (ga : GC (level t n) (.map X)) (gb : GC (level t n) (.map Y))
    (la : DE (level t n).E (lower (.map X))) (ua : DE (level t n).E (upper (.map X)))
    (lb : DE (level t n).E (lower (.map Y))) (ub : DE (level t n).E (upper (.map Y))) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) =
      .ok (boolAtom (bp (SubN t n (lower (.map X)) (lower (.map Y)) ∧ SubN t n (upper (.map X)) (upper (.map Y))))) := by
  have iX := gc_inv_n ga
  have iY := gc_inv_n gb
  cases hx : mapLookup X (.atom "dynamic") with
  | none =>
    have eX : lower (.map X) = .map X := by simp [lower, rmDyn_static hx]
    have uX : upper (.map X) = .map X := by simp [upper, hx]
    rw [eX] at la iX ⊢; rw [uX] at iX ⊢
    cases hy : mapLookup Y (.atom "dynamic") with
    | none =>
      have eY : lower (.map Y) = .map Y := by simp [lower, rmDyn_static hy]
      have uY : upper (.map Y) = .map Y := by simp [upper, hy]
      rw [eY] at lb ⊢; rw [uY]
      rw [next_sub la lb hm, bp_congr (and_self_iff (a := SubN t n (.map X) (.map Y))).symm]
    | some Dy =>
      have run := sstatic_sub (de_tc la) (de_tc lb) (m := m) (by omega)
      rw [next_sub la lb hm] at run
      have e : SubN t n (.map X) (lower (.map Y)) ∧ SubN t n (.map X) (upper (.map Y)) ↔
          SubN t n (.map X) (lower (.map Y)) := ⟨fun h => h.1, fun h => ⟨h, fun v hv => iY v (h v hv)⟩⟩
      rw [bp_congr e]
      simp only [lower] at run ⊢
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», Erlang.maps.«remove/2»]
      simpa [rmDyn] using run
  | some Dx =>
    cases hy : mapLookup Y (.atom "dynamic") with
    | none =>
      have eY : lower (.map Y) = .map Y := by simp [lower, rmDyn_static hy]
      have uY : upper (.map Y) = .map Y := by simp [upper, hy]
      rw [eY] at lb ⊢; rw [uY]
      have run := sstatic_sub (de_tc ua) (de_tc lb) (m := m) (by omega)
      rw [next_sub ua lb hm, upper_dyn hx] at run
      have e : SubN t n (lower (.map X)) (.map Y) ∧ SubN t n (upper (.map X)) (.map Y) ↔
          SubN t n (upper (.map X)) (.map Y) := ⟨fun h => h.2, fun h => ⟨fun v hv => h v (iX v hv), h⟩⟩
      rw [bp_congr e, upper_dyn hx]
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», map_get_dyn hx, run]
    | some Dy =>
      have r₁ := next_esub ua ub hm
      have r₂ := next_esub la lb hm
      rw [upper_dyn hx, upper_dyn hy] at r₁
      rw [upper_dyn hx, upper_dyn hy]
      simp only [lower] at r₂ ⊢
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      by_cases same : compareExact (fuel (.map Y) (.map X)) (.map Y) (.map X) = .eq
      · have cg := fun v => gc_congr gb ga (compare_eq_of_compareExact_eq _ _ same) (toTPN v)
        have P : SubN t n (.map (rmDyn X)) (.map (rmDyn Y)) ∧ SubN t n Dx Dy := by
          refine ⟨fun v h => ?_, fun v h => ?_⟩
          · have := (cg v).1.mpr ((denD_rmDyn X (toTPN v)).mp h)
            exact (denD_rmDyn Y (toTPN v)).mpr this
          · have := (cg v).2.mpr (by rw [upper_dyn hx]; exact h)
            rw [upper_dyn hy] at this; exact this
        simp [Erlang.erlang.«=:=/2», same, bp_true.mpr P]
      · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, hx, hy, r₁, Erlang.maps.«remove/2», Lynx.Except.andAlso]
        rw [← rmDyn, ← rmDyn, r₂]
        by_cases h₁ : SubN t n Dx Dy <;> by_cases h₂ : SubN t n (.map (rmDyn X)) (.map (rmDyn Y)) <;>
          simp [h₁, h₂, boolAtom]

/-- The unfolded top type is a static map holding every point of the next level. -/
theorem termN (t : Term) (n : Nat) : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    GC (level t n) (.map T) ∧ DE (level t n).E (.map T) ∧ lower (.map T) = .map T ∧ upper (.map T) = .map T ∧
    ∀ v : PN t n, denD (.map T) v := by
  obtain ⟨T, term, sT, -, -⟩ := termT (level t n)
  obtain ⟨T', term', sT', -, -, all⟩ := termC (FV := FVal (level t n).E (level t n).den) (kinds (level t n).ef)
    (Fn := FunA (level t n).E) funA_top
  rw [term] at term'
  cases term'
  exact ⟨T, term, GC.tc (Or.inr ⟨T, rfl, sT⟩), Or.inr ⟨T, rfl, sT'⟩, by simp [lower, rmDyn_static sT.static],
    upper_tc (Or.inr ⟨T, rfl, sT⟩), fun v => (denD_map v).mpr (all _ v.2.1 _ v.2.2)⟩

/-- A gradual type, with the top type as its unfolded map. -/
theorem gc_map {a : Term} (ga : GC (level t n) a) (la : DE (level t n).E (lower a)) (ua : DE (level t n).E (upper a)) :
    ∃ X, GC (level t n) (.map X) ∧ DE (level t n).E (lower (.map X)) ∧ DE (level t n).E (upper (.map X)) ∧
      (∀ v : PN t n, denD (lower a) v ↔ denD (lower (.map X)) v) ∧
      (∀ v : PN t n, denD (upper a) v ↔ denD (upper (.map X)) v) ∧
      (a = .atom "term" ∧ Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map X) ∨ a = .map X) := by
  rcases ga.shape with rfl | ⟨X, rfl⟩
  · obtain ⟨T, term, gT, dT, lT, uT, all⟩ := termN t n
    refine ⟨T, gT, by rw [lT]; exact dT, by rw [uT]; exact dT, fun v => ?_, fun v => ?_, Or.inl ⟨rfl, term⟩⟩
    · rw [lT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩
    · rw [uT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩
  · exact ⟨X, ga, la, ua, fun v => Iff.rfl, fun v => Iff.rfl, Or.inr rfl⟩

/-- Gradual subtyping compares both bounds exactly, on types whose function types are arrows. -/
theorem gd_sub {a b : Term} (ga : GC (level t n) a) (gb : GC (level t n) b)
    (la : DE (level t n).E (lower a)) (ua : DE (level t n).E (upper a))
    (lb : DE (level t n).E (lower b)) (ub : DE (level t n).E (upper b)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b =
      .ok (boolAtom (bp (SubN t n (lower a) (lower b) ∧ SubN t n (upper a) (upper b)))) := by
  obtain ⟨X, gX, lX, uX, elX, euX, sa⟩ := gc_map ga la ua
  obtain ⟨Y, gY, lY, uY, elY, euY, sb⟩ := gc_map gb lb ub
  have e : SubN t n (lower a) (lower b) ∧ SubN t n (upper a) (upper b) ↔
      SubN t n (lower (.map X)) (lower (.map Y)) ∧ SubN t n (upper (.map X)) (upper (.map Y)) := by
    simp only [SubN]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun v h => (elY v).mp (h₁ v ((elX v).mpr h)), fun v h => (euY v).mp (h₂ v ((euX v).mpr h))⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun v h => (elY v).mpr (h₁ v ((elX v).mp h)), fun v h => (euY v).mpr (h₂ v ((euX v).mp h))⟩
  rw [bp_congr e, ← gd_sub_maps gX gY lX uX lY uY hm]
  rcases sa with ⟨rfl, term⟩ | rfl <;> rcases sb with ⟨rfl, term'⟩ | rfl
  · rw [subtype_term_l term, subtype_term_r term']
  · rw [subtype_term_l term]
  · rw [subtype_term_r term']
  · rfl

/-- Walks whose common fields all intersect into dropped or empty fields find no common field. -/
theorem iter_disj_false (K' : Nat) (B : List (Term × Term)) :
    ∀ es : List (Term × Term), (∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∀ d', K' ≤ d' → ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/2» (D d') e.1 w = .ok (.atom "true"))) →
    ∀ m, K' + es.length ≤ m →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2» (D m) it (.map B)) = .ok (.atom "false") := by
  intro es
  induction es with
  | nil =>
    intro _ m _
    simp [Term.list, Erlang.maps.«next/1»]
    rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2».eq_def]
    simp
  | cons e rest ih =>
    intro calls m hm
    have calls' := fun e' (me' : e' ∈ rest) => calls e' (List.mem_cons_of_mem _ me')
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have hm' : K' + rest.length ≤ m := by simp at hm; omega
    have cont : ∀ x, (D (m + 1)).pure (.function "Elixir.Module.Types.Descr"
        "-iterator_non_disjoint_intersection?/2-fun-0-" 1
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B]) #[x] =
        (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2» (D m) it (.map B)) := by
      intro x
      rw [Erlang.program.«Elixir.Module.Types.Descr:-iterator_non_disjoint_intersection?/2-fun-0-/1».pure]
      simp [Elixir.Module.Types.Descr.«-iterator_non_disjoint_intersection?/2-fun-0-/3»]
    refine Eq.trans ?_ (ih calls' m hm')
    simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
    rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/2».eq_def]
    cases hb : mapLookup B e.1 with
    | none => simp [getMapKeys_single, hb, cont]
    | some y₀ =>
      obtain ⟨w, rw', k₀⟩ := calls e List.mem_cons_self y₀ hb (m + 1) (by simp at hm; omega)
      rcases k₀ with k | hb'
      · rcases dropped k with e₀ | e₀ <;> rw [e₀] at rw' <;>
          simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember]
      · by_cases dz : (compareExact (fuel w (.integer 0)) w (.integer 0) = .eq ∨ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq)
        · rcases dz with dz | dz <;>
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember, dz]
        · simp only [not_or] at dz
          simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember, dz.1, dz.2, hb']

end

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop} {H : Prop}

/-- `disjoint?/2` answers `true` on types without common points. -/
theorem descr_disj_complete (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hS : FS [])
    {m : Nat} (hm : K + 7 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (disj : ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D m) (.map A) (.map B) = .ok (.atom "true") := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y →
      (∀ name p, PtOkC TV LV MV FV name p →
        (dn name (mapLookup X (.atom name)) p && dn name (mapLookup Y (.atom name)) p) = Bool.false) →
      ∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∀ d', K + 1 ≤ d' → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
          (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/2» (D d') e.1 w = .ok (.atom "true")) := by
    intro X Y sX sY dXY e me y hy d' hd
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, ?_⟩
    cases kw : kept (.atom name, w)
    · exact Or.inl rfl
    · refine Or.inr ?_
      have rb := fieldC_empty_none ks fc (show K ≤ d' by omega) (k kw).1 (fun _ => hS) fun p ok => by
        have := sem p ok
        rw [keptO_true kw] at this
        rw [this, ← hx, ← hy]
        exact dXY name p ok
      simpa [Elixir.Module.Types.Descr.«empty_key?/2»] using rb
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  unfold Elixir.Module.Types.Descr.«disjoint?/2»
  simp [getMapKeys_single, stA, stB]
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2»
  by_cases g : sa > sb
  · have walk := iter_disj_false (K + 1) A (mapEntries B)
      (calls sB sA fun name p ok => by rw [Bool.and_comm]; exact disj name p ok) m (by have := descrC_six sB; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [← bind_assoc, walk]
    simp [Erlang.erlang.«not/1»]
  · have walk := iter_disj_false (K + 1) B (mapEntries A) (calls sA sB disj) m (by have := descrC_six sA; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [← bind_assoc, walk]
    simp [Erlang.erlang.«not/1»]

end

section
variable {t : Term} {n : Nat}

/-- Emptiness of types whose function types are arrows is exact. -/
theorem next_empty {a : Term} (ha : DE (level t n).E a) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (bp (∀ v : PN t n, ¬denD a v))) := by
  have ef3 := ef_next t n
  obtain ⟨b, run, sem⟩ := ef3.empty [] ha
  replace sem := sem (lh a + 1) (by omega) (safeN_nil _)
  have e : b = bp (∀ v : PN t n, ¬denD a v) := by
    cases b
    · exact (bp_false.mpr fun h => absurd (sem.mpr h) (by simp)).symm
    · exact (bp_true.mpr (sem.mp rfl)).symm
  subst e
  rcases ha with rfl | ⟨X, rfl, -⟩
  · rw [empty_term_false, bp_false.mpr fun h => h ptWit (denD_term ptWit)]
  · rw [empty_map_seen]; exact run m hm

/-- Disjointness of types whose function types are arrows is exact. -/
theorem next_disj {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b =
      .ok (boolAtom (bp (∀ v : PN t n, denD a v → denD b v → False))) := by
  have ef3 := ef_next t n
  by_cases h : ∀ v : PN t n, denD a v → denD b v → False
  · rw [bp_true.mpr h]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · rw [disjoint_term_l, next_empty hb hm, bp_true.mpr fun v hv => h v (denD_term v) hv]
    rcases hb with rfl | ⟨B, rfl, sB⟩
    · rw [disjoint_term_r, next_empty (Or.inr ⟨A, rfl, sA⟩) hm, bp_true.mpr fun v hv => h v hv (denD_term v)]
    have st := stepOf (level t n).ef (level t n).none
    refine descr_disj_complete st.ks st.fc trivial (by omega) sA sB fun name p ok => ?_
    by_cases mem : name ∈ names
    · have := h ⟨(name, p), mem, ok⟩
      simp only [denD_map] at this
      cases h₁ : dn name (mapLookup A (.atom name)) p <;> cases h₂ : dn name (mapLookup B (.atom name)) p <;>
        simp_all
    · have : mapLookup A (.atom name) = none := by
        cases hx : mapLookup A (.atom name)
        · rfl
        · obtain ⟨name', m', e⟩ := sA.keys (.atom name) (by simp [hx])
          simp only [Term.atom.injEq] at e; subst e; exact absurd m' mem
      simp [this, dn_none]
  · obtain ⟨s, run, sound⟩ := ef3.disj ha hb
    rw [run m hm, bp_false.mpr h]
    cases s
    · rfl
    · exact absurd (sound rfl) h

/-- Disjointness of gradual types is the emptiness of their intersection. -/
theorem gd_disj_empty {a b : Term} (ga : GC (level t n) a) (gb : GC (level t n) b)
    (ua : DE (level t n).E (upper a)) (ub : DE (level t n).E (upper b)) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) c = .ok (boolAtom s) := by
  obtain ⟨c, gc, run, sem, up⟩ := gc_inter ga gb (m := m) (by omega)
  refine ⟨c, bp (∀ v : PN t n, denD (upper a) v → denD (upper b) v → False), run, ?_, ?_⟩
  · rw [disj_upper _ ga gb]; exact next_disj ua ub (by omega)
  · rw [empty_upper _ gc]
    rcases up with up | ⟨j, hj, rj⟩
    · have dis : ∀ v : PN t n, denD (upper a) v → denD (upper b) v → False := fun v h₁ h₂ =>
        up (toTPN v) ((sem.2 (toTPN v)).mpr ⟨h₁, h₂⟩)
      rw [bp_true.mpr dis, tc_empty gc.up_tc (by omega) up]
      rfl
    · obtain ⟨c', dc', rc', sc', -⟩ := (ef_next t n).inter ua ub
      have e := (rc' j (by omega)).symm.trans rj
      cases e
      rw [next_empty dc' (by omega)]
      refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
      exact ⟨fun h v h₁ h₂ => h v ((sc' v).mpr ⟨h₁, h₂⟩), fun h v hv => h v ((sc' v).mp hv).1 ((sc' v).mp hv).2⟩

/-- `equal?/2` checks subtyping both ways, as gradual types equal by comparison are subtypes of each other. -/
theorem gd_equal {a b : Term} (ga : GC (level t n) a) (gb : GC (level t n) b)
    (la : DE (level t n).E (lower a)) (ua : DE (level t n).E (upper a))
    (lb : DE (level t n).E (lower b)) (ub : DE (level t n).E (upper b)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s₁ s₂, Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s₁) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) b a = .ok (boolAtom s₂) ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (boolAtom (s₁ && s₂)) := by
  have r₁ := gd_sub ga gb la ua lb ub hm
  have r₂ := gd_sub gb ga lb ub la ua hm
  refine ⟨_, _, r₁, r₂, ?_⟩
  by_cases c : Term.compare (Term.fuel a b) a b = .eq
  · have cg := fun v => gc_congr ga gb c (toTPN v)
    have lo : ∀ v : PN t n, denD (lower a) v ↔ denD (lower b) v := fun v => by
      rw [← denD_toTPN, ← denD_toTPN (lower b), denD_lower, denD_lower]; exact (cg v).1
    have up : ∀ v : PN t n, denD (upper a) v ↔ denD (upper b) v := fun v => (cg v).2
    rw [bp_true.mpr ⟨fun v => (lo v).mp, fun v => (up v).mp⟩, bp_true.mpr ⟨fun v => (lo v).mpr, fun v => (up v).mpr⟩]
    simp [Elixir.Module.Types.Descr.«equal?/2», Lynx.Except.orElse, Erlang.erlang.«==/2», c, Term.true]
  · simp [Elixir.Module.Types.Descr.«equal?/2», Lynx.Except.orElse, Lynx.Except.andAlso, Erlang.erlang.«==/2», c,
      Term.false, r₁, r₂]
    cases bp (SubN t n (lower a) (lower b) ∧ SubN t n (upper a) (upper b)) <;> rfl

end

/-- Every type is a subtype of itself. -/
theorem subtype_refl (d : Dispatcher) {a : Term} (h : a = .atom "term" ∨ ∃ X, a = .map X) :
    Elixir.Module.Types.Descr.«subtype?/2» d a a = .ok (.atom "true") := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  have maps : ∀ X : List (Term × Term), Elixir.Module.Types.Descr.«subtype?/2» d (.map X) (.map X) = .ok (.atom "true") := by
    intro X
    unfold Elixir.Module.Types.Descr.«subtype?/2»
    cases hx : mapLookup X (.atom "dynamic") <;>
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, any_key, Lynx.Except.andAlso, Erlang.erlang.«not/1»,
        Erlang.erlang.«/=/2», Elixir.Module.Types.Descr.«subtype_static?/2», Erlang.erlang.«=:=/2»]
  rcases h with rfl | ⟨X, rfl⟩
  · rw [subtype_term_l term, subtype_term_r term]; exact maps T
  · exact maps X

end Elixir.STTDescrProofsTest.Nest
