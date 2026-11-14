namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Types over the structural kinds: unions, intersections, and differences. -/

/-- Types whose fields are `FieldC`. -/
structure DescrC (Fn TF LF MF : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → ∃ name ∈ names, q = .atom name
  fields : ∀ name x, mapLookup X (.atom name) = some x → FieldC Fn TF LF MF name x

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

theorem DescrC.static {X : List (Term × Term)} (s : DescrC Fn TF LF MF X) :
    mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    obtain ⟨name, m, e⟩ := s.keys (.atom "dynamic") (by rw [h]; rfl)
    simp only [Term.atom.injEq] at e
    subst e
    simp [names] at m

theorem lh_field_le {X : List (Term × Term)} {q x : Term} (h : mapLookup X q = some x) : lh x ≤ lh (.map X) := by
  obtain ⟨e, me, rfl⟩ := entry_of_lookup h
  exact le_lh_map me

/-- Types are as high as their highest field. -/
theorem lh_descr_le {X : List (Term × Term)} {M : Nat} (keys : ∀ q, (mapLookup X q).isSome → ∃ name ∈ names, q = .atom name)
    (h : ∀ name x, mapLookup X (.atom name) = some x → lh x ≤ M) : lh (.map X) ≤ M := by
  refine lh_map_le.mpr fun e me => ?_
  have hx := mapLookup_of_mem_mapEntries me
  obtain ⟨name, -, he⟩ := keys e.1 (by simp [hx])
  rw [he] at hx
  exact h name e.2 hx

/-- Merging two types field by field, keeping fields of either. -/
theorem union_gen {slh : Prop} {L R U : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R)
    (f : Term → Term → Term → Except Exception Term)
    (look : ∀ name, (mapLookup R (.atom name) = none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
      (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = none → mapLookup U (.atom name) = some y) ∧
      (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok u →
        mapLookup U (.atom name) = some u))
    (keysU : ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome)
    (spec : ∀ name x y, FieldC Fn TF LF MF name x → FieldC Fn TF LF MF name y → ∃ u, f (.atom name) x y = .ok u ∧
      FieldC Fn TF LF MF name u ∧
      (∀ p, PtOkC TV LV MV FV name p → dn name (some u) p = (dn name (some x) p || dn name (some y) p)) ∧
      (slh → lh u ≤ max (lh x) (lh y))) :
    DescrC Fn TF LF MF U ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p)) ∧
      (slh → lh (.map U) ≤ max (lh (.map L)) (lh (.map R))) := by
  have at_name : ∀ name, (mapLookup R (.atom name) = none ∧ mapLookup U (.atom name) = mapLookup L (.atom name)) ∨
      (∃ y, mapLookup R (.atom name) = some y ∧ mapLookup L (.atom name) = none ∧ mapLookup U (.atom name) = some y) ∨
      ∃ x y u, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup U (.atom name) = some u ∧ FieldC Fn TF LF MF name u ∧
        (∀ p, PtOkC TV LV MV FV name p → dn name (some u) p = (dn name (some x) p || dn name (some y) p)) ∧
        (slh → lh u ≤ max (lh x) (lh y)) := by
    intro name
    obtain ⟨h₁, h₂, h₃⟩ := look name
    cases hR : mapLookup R (.atom name) with
    | none => exact Or.inl ⟨rfl, h₁ hR⟩
    | some y =>
      cases hL : mapLookup L (.atom name) with
      | none => exact Or.inr (Or.inl ⟨y, rfl, rfl, h₂ y hR hL⟩)
      | some x =>
        obtain ⟨u, run, fu, sem, le⟩ := spec name x y (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, u, rfl, rfl, h₃ x y u hL hR run, fu, sem, le⟩)
  have keys : ∀ q, (mapLookup U q).isSome → ∃ name ∈ names, q = .atom name := fun q h =>
    (keysU q h).elim (sL.keys q) (sR.keys q)
  refine ⟨⟨keys, fun name u hu => ?_⟩, fun name p ok => ?_, fun hs => lh_descr_le keys fun name u hu => ?_⟩
  · rcases at_name name with ⟨-, hU⟩ | ⟨y, hR, -, hU⟩ | ⟨x, y, u', -, -, hU, fu, -⟩
    · rw [hU] at hu; exact sL.fields name u hu
    · rw [hU] at hu; cases hu; exact sR.fields name _ hR
    · rw [hU] at hu; cases hu; exact fu
  · rcases at_name name with ⟨hR, hU⟩ | ⟨y, hR, hL, hU⟩ | ⟨x, y, u, hL, hR, hU, -, sem, -⟩
    · rw [hU, hR, dn_none]; simp
    · rw [hU, hR, hL, dn_none]; simp
    · rw [hU, hL, hR, sem p ok]
  · rcases at_name name with ⟨-, hU⟩ | ⟨y, hR, -, hU⟩ | ⟨x, y, u', hL, hR, hU, -, -, le⟩
    · rw [hU] at hu; have := lh_field_le hu; omega
    · rw [hU] at hu; cases hu; have := lh_field_le hR; omega
    · rw [hU] at hu; cases hu
      have := le hs; have := lh_field_le hL; have := lh_field_le hR; omega

/-- Plain unions of types. -/
theorem descr_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) (.map L) (.map R) = .ok (.map U) ∧
      DescrC Fn TF LF MF U ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p)) ∧
      (H → lh (.map U) ≤ max (lh (.map L)) (lh (.map R))) := by
  obtain ⟨U, run, look⟩ := union_any m L R sL.static sR.static (fun q h => by
      obtain ⟨name, -, e⟩ := sR.keys q h; exact ⟨name, e⟩)
    (fun q x y hx hy => by
      obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
      obtain ⟨u, run, -⟩ := fieldC_union ks fc hm (sL.fields name x hx) (sR.fields name y hy)
      exact ⟨u, run⟩)
  have keysU : ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome := by
    intro q h
    obtain ⟨h₁, h₂, h₃⟩ := look q
    cases hR : mapLookup R q with
    | none => rw [h₁ hR] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  obtain ⟨cU, sem, lh⟩ := union_gen (slh := H) sL sR (fun q x y => Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y)
    (fun name => ⟨(look _).1, (look _).2.1, (look _).2.2⟩) keysU
    (fun name x y fx fy => let ⟨u, run, fu, sem, le⟩ := fieldC_union ks fc hm fx fy; ⟨u, run, fu, sem, le⟩)
  exact ⟨U, run, cU, sem, lh⟩

/-- Optimized unions of types. -/
theorem descr_opt_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) (S : List (Term × Term)) :
    ∃ U, Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) (.map L) (.map R) (.map S) = .ok (.map U) ∧
      DescrC Fn TF LF MF U ∧
      ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p) := by
  obtain ⟨U, run, look, keysU⟩ := opt_union_lookup m L R (.map S) sL.static sR.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨u, run, -⟩ := fieldC_opt_union ks fc hm (sL.fields name x hx) (sR.fields name y hy) S
    exact ⟨u, run⟩
  obtain ⟨cU, sem, -⟩ := union_gen (slh := False) sL sR
    (fun q x y => Elixir.Module.Types.Descr.«opt_union/4» (D m) q x y (.map S)) look keysU
    (fun name x y fx fy => let ⟨u, run, fu, sem⟩ := fieldC_opt_union ks fc hm fx fy S; ⟨u, run, fu, sem, False.elim⟩)
  exact ⟨U, run, cU, sem⟩

/-- Intersecting two types field by field, keeping fields of both. -/
theorem inter_gen {slh : Prop} {L R I : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R)
    (f : Term → Term → Term → Except Exception Term)
    (look : ∀ name, (mapLookup L (.atom name) = none → mapLookup I (.atom name) = none) ∧
      (mapLookup R (.atom name) = none → mapLookup I (.atom name) = none) ∧
      (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok w →
        mapLookup I (.atom name) = keptO name w))
    (keysI : ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome)
    (spec : ∀ name x y, FieldC Fn TF LF MF name x → FieldC Fn TF LF MF name y → ∃ w, f (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (slh → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)) :
    DescrC Fn TF LF MF I ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p)) ∧
      (slh → lh (.map I) ≤ max (lh (.map L)) (lh (.map R))) := by
  have at_name : ∀ name, (mapLookup L (.atom name) = none ∧ mapLookup I (.atom name) = none) ∨
      (mapLookup R (.atom name) = none ∧ mapLookup I (.atom name) = none) ∨
      ∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup I (.atom name) = keptO name w ∧
        (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (slh → lh w ≤ max (lh x) (lh y))) ∧
        (∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)) := by
    intro name
    obtain ⟨h₁, h₂, h₃⟩ := look name
    cases hL : mapLookup L (.atom name) with
    | none => exact Or.inl ⟨rfl, h₁ hL⟩
    | some x =>
      cases hR : mapLookup R (.atom name) with
      | none => exact Or.inr (Or.inl ⟨rfl, h₂ hR⟩)
      | some y =>
        obtain ⟨w, run, k, sem⟩ := spec name x y (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, w, rfl, rfl, h₃ x y w hL hR run, k, sem⟩)
  have keys : ∀ q, (mapLookup I q).isSome → ∃ name ∈ names, q = .atom name := fun q h => sL.keys q (keysI q h)
  refine ⟨⟨keys, fun name w hw => ?_⟩, fun name p ok => ?_, fun hs => lh_descr_le keys fun name w hw => ?_⟩
  · rcases at_name name with ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨x, y, w', -, -, hI, k, -⟩
    · rw [hI] at hw; cases hw
    · rw [hI] at hw; cases hw
    · rw [hI] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw; exact (k kw).1
  · rcases at_name name with ⟨hL, hI⟩ | ⟨hR, hI⟩ | ⟨x, y, w, hL, hR, hI, -, sem⟩
    · rw [hI, hL, dn_none]; simp
    · rw [hI, hR, dn_none]; simp
    · rw [hI, hL, hR, sem p ok]
  · rcases at_name name with ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨x, y, w', hL, hR, hI, k, -⟩
    · rw [hI] at hw; cases hw
    · rw [hI] at hw; cases hw
    · rw [hI] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw
        have := (k kw).2 hs; have := lh_field_le hL; have := lh_field_le hR; omega

/-- Plain intersections of types. -/
theorem descr_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) :
    ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map L) (.map R) = .ok (.map I) ∧
      DescrC Fn TF LF MF I ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p)) ∧
      (H → lh (.map I) ≤ max (lh (.map L)) (lh (.map R))) := by
  obtain ⟨I, run, look, keysI⟩ := inter_lookup m L R sL.static sR.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := fieldC_inter ks fc hm (sL.fields name x hx) (sR.fields name y hy)
    exact ⟨w, run⟩
  obtain ⟨cI, sem, lh⟩ := inter_gen (slh := H) sL sR
    (fun q x y => Elixir.Module.Types.Descr.«bare_intersection/3» (D m) q x y)
    (fun name => ⟨(look name).1, (look name).2.1, fun x y w hx hy r => by rw [(look name).2.2 x y w hx hy r]; rfl⟩)
    keysI (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy;
      ⟨w, run, fun kw => ⟨(k kw).1, (k kw).2⟩, sem⟩)
  exact ⟨I, run, cI, sem, lh⟩

/-- Optimized intersections of types. -/
theorem descr_opt_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) (S : List (Term × Term)) :
    ∃ I, Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) (.map L) (.map R) (.map S) = .ok (.map I) ∧
      DescrC Fn TF LF MF I ∧
      ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p) := by
  obtain ⟨I, run, look, keysI⟩ := opt_inter_lookup m L R (.map S) sL.static sR.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := fieldC_opt_inter ks fc hm (sL.fields name x hx) (sR.fields name y hy) S
    exact ⟨w, run⟩
  obtain ⟨cI, sem, -⟩ := inter_gen (slh := False) sL sR
    (fun q x y => Elixir.Module.Types.Descr.«opt_intersection/4» (D m) q x y (.map S))
    (fun name => ⟨(look name).1, (look name).2.1, fun x y w hx hy r => by rw [(look name).2.2 x y w hx hy r]; rfl⟩)
    keysI (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_opt_inter ks fc hm fx fy S;
      ⟨w, run, fun kw => ⟨k kw, False.elim⟩, sem⟩)
  exact ⟨I, run, cI, sem⟩

/-- Folding the differences of fields, which keeps the fields of the first type outside the second. -/
theorem diff_gen {slh : Prop} (depth : Nat) (fn : Term) (f : Term → Term → Term → Except Exception Term)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R)
    (call : ∀ q v₁ v₂, Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[q, v₁, v₂] =
      f q v₁ v₂)
    (spec : ∀ name x y, FieldC Fn TF LF MF name x → FieldC Fn TF LF MF name y → ∃ w, f (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧
        (slh → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)) :
    ∃ O, (mapEntries R).foldlM (fun acc entry =>
        (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
          (.function "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3 #[fn]) #[entry.1, entry.2, acc] :
          Except Exception Term)) (.map L) = .ok (.map O) ∧
      DescrC Fn TF LF MF O ∧ (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup O (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && !dn name (mapLookup R (.atom name)) p)) ∧
      (slh → lh (.map O) ≤ max (lh (.map L)) (lh (.map R))) := by
  let g : Term → Term → Term → Term := fun q v₁ v₂ =>
    match f q v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y w, f q x y = .ok w → g q x y = w := by intro q x y w run; simp [g, run]
  obtain ⟨O, fold, lookO, -⟩ := difference_fold depth fn g (mapEntries R) L (mapEntries_distinct R) (by
    intro e member v₁ found
    have hy := mapLookup_of_mem_mapEntries member
    obtain ⟨name, -, he⟩ := sR.keys e.1 (by simp [hy])
    rw [he] at hy found ⊢
    obtain ⟨w, run, -⟩ := spec name v₁ e.2 (sL.fields name v₁ found) (sR.fields name e.2 hy)
    rw [call, run, value _ _ _ _ run])
  have look := lookup_fold lookO
  have at_name : ∀ name, (mapLookup R (.atom name) = none ∧ mapLookup O (.atom name) = mapLookup L (.atom name)) ∨
      (mapLookup L (.atom name) = none ∧ mapLookup O (.atom name) = none) ∨
      ∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup O (.atom name) = keptO name w ∧
        (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧
          (slh → lh w ≤ max (lh x) (lh y))) ∧
        ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p) := by
    intro name
    rw [look name]
    cases hR : mapLookup R (.atom name) with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some y =>
      cases hL : mapLookup L (.atom name) with
      | none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | some x =>
        obtain ⟨w, run, k, d⟩ := spec name x y (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, w, rfl, rfl, by simp [value _ _ _ _ run, keptO], k, d⟩)
  have keysO : ∀ q, (mapLookup O q).isSome → ∃ name ∈ names, q = .atom name := by
    intro q h
    rw [lookO] at h
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [hit] at h; exact sL.keys q h
    | some e =>
      rw [hit] at h
      obtain ⟨qe, -⟩ := find_entry hit
      cases hl : mapLookup L e.1 with
      | none => simp [hl] at h
      | some x =>
        obtain ⟨name, m, he⟩ := sL.keys e.1 (by simp [hl])
        rw [he] at qe
        exact ⟨name, m, (compareExact_eq_atom q name).mp qe⟩
  refine ⟨O, by simpa using fold, ⟨keysO, fun name w hw => ?_⟩, fun name p ok => ?_, fun hs => ?_⟩
  · rcases at_name name with ⟨-, hO⟩ | ⟨-, hO⟩ | ⟨x, y, w', -, -, hO, k, -⟩
    · rw [hO] at hw; exact sL.fields name w hw
    · rw [hO] at hw; cases hw
    · rw [hO] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw; exact (k kw).1
  · rcases at_name name with ⟨hR, hO⟩ | ⟨hL, hO⟩ | ⟨x, y, w, hL, hR, hO, -, d⟩
    · rw [hO, hR, dn_none]; simp
    · rw [hO, hL, dn_none]; simp
    · rw [hO, hL, hR, d p ok]
  · refine lh_descr_le keysO fun name w hw => ?_
    rcases at_name name with ⟨-, hO⟩ | ⟨-, hO⟩ | ⟨x, y, w', hL, hR, hO, k, -⟩
    · rw [hO] at hw; have := lh_field_le hw; omega
    · rw [hO] at hw; cases hw
    · rw [hO] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw
        have := (k kw).2 hs; have := lh_field_le hL; have := lh_field_le hR; omega

/-- Plain differences of types. -/
theorem descr_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) :
    ∃ O, Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map L) (.map R) = .ok (.map O) ∧
      DescrC Fn TF LF MF O ∧ (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup O (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && !dn name (mapLookup R (.atom name)) p)) ∧
      (H → lh (.map O) ≤ max (lh (.map L)) (lh (.map R))) := by
  by_cases nR : R = []
  · subst nR
    refine ⟨L, by unfold Elixir.Module.Types.Descr.«bare_difference/2»; simp [Erlang.erlang.«==/2»], sL,
      fun name p _ => by simp [mapLookup, dn_none], by omega⟩
  obtain ⟨O, fold, sO, dO, lO⟩ := diff_gen (slh := H) m
    (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    (fun q x y => Elixir.Module.Types.Descr.«bare_difference/3» (D m) q x y) sL sR
    (fun q x y => by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure])
    (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy;
      ⟨w, run, fun kw => ⟨(k kw).1, (k kw).2⟩, sem⟩)
  refine ⟨O, ?_, sO, dO, lO⟩
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sL.static, static_map sR.static, nR]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», nR, Erlang.maps.«fold/3»]
  simpa using fold

/-- Optimized differences of types. -/
theorem descr_opt_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) (S : List (Term × Term)) :
    ∃ O, Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 2)) (.map L) (.map R) (.map S) = .ok (.map O) ∧
      DescrC Fn TF LF MF O ∧ ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup O (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && !dn name (mapLookup R (.atom name)) p) := by
  by_cases nR : R = []
  · subst nR
    refine ⟨L, by unfold Elixir.Module.Types.Descr.«opt_difference/3»; simp [Erlang.erlang.«==/2»], sL,
      fun name p _ => by simp [mapLookup, dn_none]⟩
  obtain ⟨O, fold, sO, dO, -⟩ := diff_gen (slh := False) m
    (.function "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-0-" 3 #[.map S])
    (fun q x y => Elixir.Module.Types.Descr.«opt_difference/4» (D m) q x y (.map S)) sL sR
    (fun q x y => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-opt_difference/3-anonymous-0-/4»])
    (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_opt_diff ks fc hm fx fy S;
      ⟨w, run, fun kw => ⟨k kw, False.elim⟩, sem⟩)
  refine ⟨O, ?_, sO, dO⟩
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sL.static, static_map sR.static, nR]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», nR, Erlang.maps.«fold/3»]
  simpa using fold

end

end Elixir.STTDescrProofsTest.Nest
