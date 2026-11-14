namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types of one level give element types of the next. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem de_none : DE E (.map []) := Or.inr ⟨[], rfl, descrC_nil⟩

end

section
variable {nd : Term} {C : Nat → Term → Prop} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

/-- Maps that combine the node with types of height zero: a tuple field of the expansion literal of `nd`, and
other fields of height zero. -/
def ComboMap (nd : Term) (X : List (Term × Term)) : Prop :=
  (∀ w, mapLookup X (.atom "tuple") = some w → OField (PureLit nd) w) ∧
    ∀ name w, name ≠ "tuple" → mapLookup X (.atom name) = some w → lh w = 0

theorem isT_map {nd : Term} {X : List (Term × Term)} : ¬IsT nd (.map X) := by
  rintro ⟨-, h⟩
  unfold «recursive_node?/1» at h
  simp at h

theorem combo_map {nd : Term} {X : List (Term × Term)} : Combo nd (.map X) ↔ ComboMap nd X := by
  constructor
  · rintro (h | h | ⟨Y, h, ct, co⟩)
    · cases h
    · exact absurd h isT_map
    · cases h; exact ⟨ct, co⟩
  · exact fun ⟨ct, co⟩ => Or.inr (Or.inr ⟨X, rfl, ct, co⟩)

/-- Pure tuple fields of `TF`. -/
abbrev TFc (nd : Term) (TF : Term → Prop) (x : Term) : Prop := TF x ∧ OField (PureLit nd) x

/-- Fields of height zero of `F`. -/
abbrev ZF (F : Term → Prop) (x : Term) : Prop := F x ∧ lh x = 0

theorem comboMap_descr {nd : Term} {Fn TF LF MF : Term → Prop} {X : List (Term × Term)}
    (fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT)
    (sX : DescrC Fn TF LF MF X) (c : ComboMap nd X) : DescrC FunTop (TFc nd TF) (ZF LF) (ZF MF) X := by
  refine ⟨sX.keys, fun name x hx => ?_⟩
  have f := sX.fields name x hx
  by_cases nt : name = "tuple"
  · subst nt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fieldC_tuple f, c.1 x hx⟩))))
  have z := c.2 name x nt hx
  rcases f with ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩
  · exact Or.inl ⟨h, f⟩
  · exact Or.inr (Or.inl ⟨h, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, fz f z⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f, z⟩)))
  · exact absurd h nt
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, f, z⟩))))

theorem descr_comboMap {nd : Term} {TF LF MF : Term → Prop} {X : List (Term × Term)}
    (sX : DescrC FunTop (TFc nd TF) (ZF LF) (ZF MF) X) : ComboMap nd X := by
  refine ⟨fun w hw => (fieldC_tuple (sX.fields _ w hw)).2, fun name w nt hw => ?_⟩
  rcases sX.fields name w hw with ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨h, -⟩ | ⟨-, f⟩
  · exact lh_bitF f
  · exact lh_atomF f
  · rw [show w = funTopT from f]; exact lh_funTop
  · exact f.2
  · exact absurd h nt
  · exact f.2

theorem descr_unrestrict' {nd : Term} {TF LF MF : Term → Prop} {name : String} {x : Term}
    (f : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name x) : FieldC FunTop TF LF MF name x := by
  rcases f with ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩
  · exact Or.inl ⟨h, f⟩
  · exact Or.inr (Or.inl ⟨h, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, f⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f.1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, f.1⟩))))

/-- Plain operations on fields keep pure tuple fields pure and fields of height zero at height zero. -/
theorem restrict_field {nd : Term} {TF LF MF : Term → Prop} {name : String} {x y w : Term}
    (fx : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name x) (fy : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name y)
    (fw : FieldC FunTop TF LF MF name w) (lw : lh w ≤ max (lh x) (lh y))
    (pw : name = "tuple" → OField (PureLit nd) w) : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name w := by
  rcases fw with ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩
  · exact Or.inl ⟨h, f⟩
  · exact Or.inr (Or.inl ⟨h, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, f⟩))
  · subst h
    have := (fieldC_list fx).2
    have := (fieldC_list fy).2
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, f, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f, pw h⟩))))
  · subst h
    have := (fieldC_map fx).2
    have := (fieldC_map fy).2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, f, by omega⟩))))

/-- Plain intersections of combinations of the node with types of height zero are such combinations. -/
theorem combo_inter {nd : Term} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
    (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K FunTop FVT (fun _ => True) True)
    (fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT) {m : Nat} (hm : K + 1 ≤ m)
    {A B I : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (cA : ComboMap nd A) (cB : ComboMap nd B)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) (.map B) = .ok (.map I)) :
    ComboMap nd I := by
  have sA' := comboMap_descr fz sA cA
  have sB' := comboMap_descr fz sB cB
  obtain ⟨I', run', look, keysI⟩ := inter_lookup m A B sA.static sB.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sA.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := fieldC_inter ks fc hm (descr_unrestrict' (sA'.fields name x hx))
      (descr_unrestrict' (sB'.fields name y hy))
    exact ⟨w, run⟩
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Term.map.injEq] at e
  subst e
  obtain ⟨cI, -, -⟩ := inter_gen (slh := True) (TV := TV) (LV := LV) (MV := MV) sA' sB'
    (fun q x y => Elixir.Module.Types.Descr.«bare_intersection/3» (D m) q x y)
    (fun name => ⟨(look name).1, (look name).2.1, fun x y w hx hy r => by rw [(look name).2.2 x y w hx hy r]; rfl⟩)
    keysI (fun name x y fx fy => by
      obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm (descr_unrestrict' fx) (descr_unrestrict' fy)
      refine ⟨w, run, fun kw => ⟨restrict_field fx fy (k kw).1 ((k kw).2 trivial) fun h => ?_, fun _ => (k kw).2 trivial⟩,
        sem⟩
      subst h
      obtain ⟨w', run'', kk, -⟩ := open_inter_spec pureLit_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
        tuple_inter_shape.2.2 (.atom "tuple") (fieldC_tuple fx).2 (fieldC_tuple fy).2
      have : w = w' := by
        have := run.symm.trans (by simpa [Elixir.Module.Types.Descr.«bare_intersection/3»] using run'')
        simpa using this
      subst this
      exact (kk kw).1)
  exact descr_comboMap cI

/-- Plain differences of combinations of the node with types of height zero are such combinations. -/
theorem combo_diff {nd : Term} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
    (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K FunTop FVT (fun _ => True) True)
    (fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT) {m : Nat} (hm : K + 2 ≤ m)
    {A B O : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (cA : ComboMap nd A) (cB : ComboMap nd B)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map A) (.map B) = .ok (.map O)) :
    ComboMap nd O := by
  by_cases nB : B = []
  · subst nB
    have : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map A) (.map []) = .ok (.map A) := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»; simp [Erlang.erlang.«==/2»]
    rw [this] at run
    simp only [Except.ok.injEq, Term.map.injEq] at run
    subst run
    exact cA
  have sA' := comboMap_descr fz sA cA
  have sB' := comboMap_descr fz sB cB
  obtain ⟨O', fold, sO, -, -⟩ := diff_gen (slh := True) (TV := TV) (LV := LV) (MV := MV) m
    (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    (fun q x y => Elixir.Module.Types.Descr.«bare_difference/3» (D m) q x y) sA' sB'
    (fun q x y => by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure])
    (fun name x y fx fy => by
      obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm (descr_unrestrict' fx) (descr_unrestrict' fy)
      refine ⟨w, run, fun kw => ⟨restrict_field fx fy (k kw).1 ((k kw).2 trivial) fun h => ?_, fun _ => (k kw).2 trivial⟩,
        sem⟩
      subst h
      obtain ⟨w', run'', fw', -⟩ := pure_diff_sem (fieldC_tuple fx).2 (fieldC_tuple fy).2
      have : w = w' := by
        have := run.symm.trans (by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run'')
        simpa using this
      subst this
      exact fw')
  have run' : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map A) (.map B) = .ok (.map O') := by
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map sA.static, static_map sB.static, nB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nB, Erlang.maps.«fold/3»]
    simpa using fold
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Term.map.injEq] at e
  subst e
  exact descr_comboMap sO

section
variable {nd : Term} {C : Nat → Term → Prop} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

theorem dg_low (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a : Term} (ha : DEG Fn TF LF MF a) (z : lh a = 0) : Combo nd a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  refine combo_map.mpr ⟨fun w hw => ?_, fun name w _ hw => ?_⟩
  · obtain ⟨k, rfl⟩ := st.tz (fieldC_tuple (sX.fields _ w hw)) (by have := lh_field_le hw; omega)
    exact Or.inl ⟨k, rfl⟩
  · have := lh_field_le hw; omega

theorem dg_cinter (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b c : Term} {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 14 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) : Combo nd c := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [inter_term_left] at run; cases run; exact cb
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [inter_term_right] at run; cases run; exact ca
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨I, runI, -, -, -⟩ := descr_inter st.ks st.fc (m := m') (by omega) sA sB
  rw [runI] at run; cases run
  exact combo_map.mpr (combo_inter st.ks (fcOf K) st.fz (by omega) sA sB (combo_map.mp ca) (combo_map.mp cb) runI)

theorem dg_cdiff (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b c : Term} {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 14 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) : Combo nd c := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [diff_term_right] at run; cases run; exact combo_none nd
  by_cases nB : B = []
  · subst nB
    rw [diff_none_right _ ha] at run; cases run; exact ca
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, lT, -⟩ := termC (FV := FV) st.ks st.ftop
    rw [diff_term_left _ term sT.static sB.static nB] at run
    obtain ⟨O, runO, -, -, -⟩ := descr_diff st.ks st.fc (m := m') (by omega) sT sB
    rw [runO] at run; cases run
    have cT : ComboMap nd T := ⟨fun w hw => by
        obtain ⟨k, rfl⟩ := st.tz (fieldC_tuple (sT.fields _ w hw)) (by have := lh_field_le hw; omega)
        exact Or.inl ⟨k, rfl⟩,
      fun name w _ hw => by have := lh_field_le hw; omega⟩
    exact combo_map.mpr (combo_diff st.ks (fcOf K) st.fz (by omega) sT sB cT (combo_map.mp cb) runO)
  · obtain ⟨O, runO, -, -, -⟩ := descr_diff st.ks st.fc (m := m') (by omega) sA sB
    rw [runO] at run; cases run
    exact combo_map.mpr (combo_diff st.ks (fcOf K) st.fz (by omega) sA sB (combo_map.mp ca) (combo_map.mp cb) runO)

theorem map_topk_nonempty (d : Dispatcher) (k : Int) {S : List (Term × Term)}
    (fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") (.tuple #[.integer k, .atom "open", .nil])) e.1) (.cons (.atom "map") (.tuple #[.integer k, .atom "open", .nil])) e.1 == .eq) =
      Bool.false) :
    Elixir.Module.Types.Descr.«map_empty?/2» d (.tuple #[.integer k, .atom "open", .nil]) (.map S) = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]
  rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
  have line := line_inter_open d k .nil
  simp [line, Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil]
  rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
  simp

/-- Combinations of the node with types of height zero decide their emptiness exactly, when no seen BDD is a tuple
BDD of the expansion literal. -/
theorem dg_cempty (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool}
    (ha : DEG Fn TF LF MF a) (ca : Combo nd a) (hS : Safe1 nd S) (hm : K + 14 ≤ m)
    (run : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v : PtG TV LV MV FV, ¬denD a v := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · rw [empty_term] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    exact ⟨fun h => absurd h (by decide), fun h => absurd (denD_term ptWit) (h ptWit)⟩
  have cX := combo_map.mp ca
  by_cases ne : X = []
  · subst ne
    rw [empty_none_seen] at run
    have : b = Bool.true := by cases b <;> simp_all [boolAtom]
    subst this
    exact ⟨fun _ v => by simp [denD_map, mapLookup, dn_none], fun _ => rfl⟩
  have fresh : ∀ x, OField (PureLit nd) x →
      S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 == .eq) = Bool.false := by
    intro x px
    simp only [List.any_eq_false, beq_iff_eq]
    exact fun e me => hS.2 e me x px
  have ht : ∀ x, mapLookup X (.atom "tuple") = some x → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      .ok (boolAtom (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false))) := fun x hx =>
    pure_empty_val (cX.1 x hx) (fresh x (cX.1 x hx)) (safeN_noid hS.1 _) (by omega)
  have hmf : ∀ x, mapLookup X (.atom "map") = some x → Elixir.Module.Types.Descr.«map_empty?/2» (D m) x (.map S) =
      .ok (boolAtom Bool.false) := fun x hx => by
    obtain ⟨k, rfl⟩ := st.mz (fieldC_map (sX.fields _ x hx)) (cX.2 "map" x (by decide) hx)
    exact map_topk_nonempty _ k (not_seen hS.1 (by simp [lh]) "map")
  have hl : ∀ x, mapLookup X (.atom "list") = some x → Elixir.Module.Types.Descr.«list_empty?/2» (D m) x (.map S) =
      .ok (boolAtom Bool.false) := fun x hx => by
    rw [st.lz (fieldC_list (sX.fields _ x hx)) (cX.2 "list" x (by decide) hx)]
    exact list_top_nonempty _ _
  have hf : ∀ x, mapLookup X (.atom "fun") = some x → Elixir.Module.Types.Descr.«fun_empty?/2» (D m) x (.map S) =
      .ok (boolAtom Bool.false) := fun x hx => by
    have hx' : FunTop x := st.fz (fieldC_fun (sX.fields _ x hx)) (cX.2 "fun" x (by decide) hx)
    rw [hx']
    exact fun_top_nonempty _ _
  obtain ⟨bt, ht', hbt⟩ : ∃ bt : Bool, (∀ x, mapLookup X (.atom "tuple") = some x →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom bt)) ∧
      ∀ x, mapLookup X (.atom "tuple") = some x → bt = (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)) := by
    cases h : mapLookup X (.atom "tuple") with
    | none => exact ⟨Bool.true, fun x hx => by simp at hx, fun x hx => by simp at hx⟩
    | some x =>
      refine ⟨(!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)), fun x' hx' => ?_, fun x' hx' => ?_⟩
      · simp only [Option.some.injEq] at hx'; subst hx'; exact ht x h
      · simp only [Option.some.injEq] at hx'; subst hx'; rfl
  rw [descr_empty_run (D m) sX.static ne ht' hmf hl hf] at run
  have hb : b = (!(mapLookup X (.atom "atom")).isSome && !(mapLookup X (.atom "bitmap")).isSome &&
      ((mapLookup X (.atom "tuple")).isNone || bt) && (mapLookup X (.atom "map")).isNone &&
      (mapLookup X (.atom "list")).isNone && (mapLookup X (.atom "fun")).isNone) := by
    simp only [boolAtom, Except.ok.injEq] at run
    cases b <;> cases h : (!(mapLookup X (.atom "atom")).isSome && !(mapLookup X (.atom "bitmap")).isSome &&
      ((mapLookup X (.atom "tuple")).isNone || bt) && (mapLookup X (.atom "map")).isNone &&
      (mapLookup X (.atom "list")).isNone && (mapLookup X (.atom "fun")).isNone) <;> simp_all
  subst hb
  have pt : ∀ (name : String) (p : Point), name ∈ names → PtOkC TV LV MV FV name p →
      dn name (mapLookup X (.atom name)) p = Bool.true → ∃ v : PtG TV LV MV FV, denD (.map X) v :=
    fun name p mn ok h => ⟨⟨(name, p), mn, ok⟩, (denD_map _).mpr h⟩
  constructor
  · intro h v hv
    rw [denD_map] at hv
    obtain ⟨⟨name, p⟩, mn, ok⟩ := v
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hbm⟩, htp⟩, hmp⟩, hlp⟩, hfp⟩ := h
    rcases names_mem mn with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [hbm, dn_none] at hv
    · simp [ha, dn_none] at hv
    · simp [hfp, dn_none] at hv
    · simp [hlp, dn_none] at hv
    · cases hx : mapLookup X (.atom "tuple") with
      | none => simp [hx, dn_none] at hv
      | some x =>
        rw [hx] at htp hv
        simp only [reduceCtorEq, false_or] at htp
        rw [hbt x hx] at htp
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at htp
        rw [dn_tuple] at hv
        obtain ⟨c, hc⟩ := pure_val (cX.1 x hx) (st.ks.t.resp _ (ok.2.2.2.1 rfl))
        rw [hc] at hv
        cases c
        · rw [htp.2] at hv; cases hv
        · rw [htp.1] at hv; cases hv
    · simp [hmp, dn_none] at hv
  · intro h
    have no : ∀ (name : String) (p : Point), name ∈ names → PtOkC TV LV MV FV name p →
        dn name (mapLookup X (.atom name)) p = Bool.true → False := fun name p mn ok d => by
      obtain ⟨v, hv⟩ := pt name p mn ok d
      exact h v hv
    have atomN : mapLookup X (.atom "atom") = none := by
      cases hx : mapLookup X (.atom "atom") with
      | none => rfl
      | some x =>
        obtain ⟨p, ok, d⟩ := atom_full (TV := TV) (LV := LV) (MV := MV) sX hx
        exact (no "atom" p (by simp [names]) ok (by rw [hx]; exact d)).elim
    have bitN : mapLookup X (.atom "bitmap") = none := by
      cases hx : mapLookup X (.atom "bitmap") with
      | none => rfl
      | some x =>
        obtain ⟨p, ok, d⟩ := bitmap_full (TV := TV) (LV := LV) (MV := MV) sX hx
        exact (no "bitmap" p (by simp [names]) ok (by rw [hx]; exact d)).elim
    have funN : mapLookup X (.atom "fun") = none := by
      cases hx : mapLookup X (.atom "fun") with
      | none => rfl
      | some x =>
        have hx' : FunTop x := st.fz (fieldC_fun (sX.fields _ x hx)) (cX.2 "fun" x (by decide) hx)
        obtain ⟨a, ρ, r, f⟩ := st.fvw
        refine (no "fun" (0, a, ρ) (by simp [names]) (ptOk_fun r f) ?_).elim
        rw [hx, hx', dn_fun]
        simp [funTopT, arityOf, mapLookup]
    have listN : mapLookup X (.atom "list") = none := by
      cases hx : mapLookup X (.atom "list") with
      | none => rfl
      | some x =>
        rw [st.lz (fieldC_list (sX.fields _ x hx)) (cX.2 "list" x (by decide) hx)] at hx
        obtain ⟨ρ, hρ⟩ := st.ks.l.wit
        refine (no "list" (0, .nil, ρ) (by simp [names])
          ⟨st.ks.l.resp ρ hρ, by simp, fun _ => hρ, by simp, by simp⟩ ?_).elim
        rw [hx, dn_list, denL_top]
    have mapN : mapLookup X (.atom "map") = none := by
      cases hx : mapLookup X (.atom "map") with
      | none => rfl
      | some x =>
        obtain ⟨k, rfl⟩ := st.mz (fieldC_map (sX.fields _ x hx)) (cX.2 "map" x (by decide) hx)
        obtain ⟨ρ, hρ⟩ := st.ks.m.wit
        refine (no "map" (0, .nil, ρ) (by simp [names])
          ⟨st.ks.m.resp ρ hρ, by simp, by simp, by simp, fun _ => hρ, by simp⟩ ?_).elim
        rw [hx, dn_map, denO_top]
    have tupB : (mapLookup X (.atom "tuple")).isNone || bt := by
      cases hx : mapLookup X (.atom "tuple") with
      | none => rfl
      | some x =>
        rw [hbt x hx]
        have fx := fieldC_tuple (sX.fields _ x hx)
        have none : ∀ c : Bool, denO x (fun _ => c) = Bool.false := by
          intro c
          cases hc : denO x (fun _ => c)
          · rfl
          · obtain ⟨ρ, hρ, e⟩ := st.treal c fx (cX.1 x hx)
            refine (no "tuple" (0, .nil, ρ) (by simp [names])
              ⟨st.ks.t.resp ρ hρ, by simp, by simp, fun _ => hρ, by simp⟩ ?_).elim
            rw [hx, dn_tuple, e, hc]
        simp [none]
    simp [atomN, bitN, funN, listN, mapN, tupB]

end

/-- Fusing types over fields `TF`, `LF`, and `MF`. -/
def FuseOk (K : Nat) (Fn TF LF MF : Term → Prop) (TV LV MV : (Term → Bool) → Prop)
    (FV : Term → (Term → Bool) → Prop) : Prop :=
  ∀ {a b : Term} (n : Int) {m : Nat}, DEG Fn TF LF MF a → DEG Fn TF LF MF b → compareExact (fuel a b) a b ≠ .eq → K + 14 ≤ m → ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ (DEG Fn TF LF MF r ∧ ∀ v : PtG TV LV MV FV, denD r v ↔ denD a v ∨ denD b v))

/-- Types over the fields of a step are element types. -/
theorem ef_gen (st : StepOk nd C K Fn TF LF MF TV LV MV FV) (fu : FuseOk K Fn TF LF MF TV LV MV FV) :
    EF nd (DEG Fn TF LF MF) (PtG TV LV MV FV) denD tlD (K + 14) where
  pos := by omega
  term := Or.inl rfl
  none := Or.inr ⟨[], rfl, descrC_nil⟩
  den_term := denD_term
  static := fun {a} ha => by
    rcases ha with rfl | ⟨X, rfl, sX⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, rfl, sX.static⟩)
  node := fun {a} ha hn => by
    rcases ha with rfl | ⟨X, rfl, -⟩ <;> obtain ⟨r, st, g, h⟩ := hn <;> simp at h
  low := fun ha z => dg_low st ha z
  cinter := fun ha hb ca cb hm run => dg_cinter st ha hb ca cb hm run
  cdiff := fun ha hb ca cb hm run => dg_cdiff st ha hb ca cb hm run
  cempty := fun ha ca hS hm run => dg_cempty st ha ca hS (by omega) run
  inhabited := ⟨ptWit⟩
  resp := fun he he' h d => de_resp st he he' h d
  union := fun ha hb => de_union st ha hb
  inter := fun ha hb =>
    let ⟨c, hc, run, sem, l⟩ := de_inter st ha hb
    ⟨c, hc, fun m hm => run m (by omega), sem, l⟩
  diff := fun ha hb =>
    let ⟨c, hc, run, sem, l⟩ := de_diff st ha hb
    ⟨c, hc, fun m hm => run m (by omega), sem, l⟩
  opt_union := by intro a b S m ha hb hm; exact de_opt_union st S ha hb (by omega)
  opt_inter := by intro a b S m ha hb hm; exact de_opt_inter st S ha hb (by omega)
  opt_diff := by intro a b S m ha hb hm; exact de_opt_diff st S ha hb (by omega)
  empty := fun S ha =>
    let ⟨b, run, ex⟩ := de_empty st S ha
    ⟨b, fun m hm => run m (by omega), ex⟩
  sub := fun ha hb => de_sub st ha hb
  subc := fun ha hb incl m hm => de_subc st ha hb incl hm
  disj := fun ha hb => de_disj st ha hb
  fuse := by intro a b n m ha hb ne hm; exact fu n ha hb ne hm
  tail := fun he => let ⟨e', run, he', sem, l⟩ := de_tail st he; ⟨e', fun m _ => run (D m), he', sem, l⟩
  tl_witness := ⟨ptWit, by simp [tlD, ptWit]⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem stepOf (ef : EF nd E V den tl K) (hnone : E (.map [])) :
    StepOk nd (fun N => NestC (EB E N)) (K + 9) (FunA E) (TField E) (LF E) (MField E) (ValT E den) (ValLN E den tl)
      (ValMN E den) (FVal E den) :=
  ⟨(kinds ef).mono (by omega), funAC ef ef.subc, funA_top, fun hx z => funA_lh0 hx z, fVal_wit,
    fun ha h => de_nest ef ha h,
    fun hN => let ⟨o, d, f⟩ := nest_ops ef hnone hN; ⟨o.mono (by omega), d.mono (by omega), f.mono (by omega)⟩,
    tz_of, lz_of ef, mz_of, fun c _ fx px => treal_of ef c fx px⟩

theorem de_fuse (ef : EF nd E V den tl K) (hnone : E (.map [])) {a b : Term} (n : Int) {m : Nat} (ha : DE E a)
    (hb : DE E b) (ne : compareExact (fuel a b) a b ≠ .eq) (hm : K + 23 ≤ m) : ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ (DE E r ∧ ∀ v : PtD E den tl (FVal E den), denD r v ↔ denD a v ∨ denD b v)) := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, fuse_term_l _ _ _, Or.inl rfl⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, fuse_term_r _ _ _, Or.inl rfl⟩
  obtain ⟨u, hu, urun, usem, -⟩ := de_union (stepOf ef hnone) (Or.inr ⟨A, rfl, sA⟩) (Or.inr ⟨B, rfl, sB⟩)
  have run := urun m hm
  obtain ⟨c₁, r₁⟩ := aob_bool (.map A)
  obtain ⟨c₂, r₂⟩ := aob_bool (.map B)
  have second : ∃ r, (do
      let _19 ← Lynx.Except.andAlso (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A))
        (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B)) Bool.true
      Lynx.Except.guard (Except.ok (_19.isMember [Term.atom "false", Term.atom "nil"]))
        (fun _ => pure (Term.atom "nil")) fun _ => Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B)) = .ok r ∧
      (r = .atom "nil" ∨ (DE E r ∧ ∀ v : PtD E den tl (FVal E den), denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
    rw [r₁, r₂]
    cases c₁ <;> cases c₂ <;>
      simp [Lynx.Except.andAlso, boolAtom, isMember, run, hu, usem]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3».eq_def]
  simp only [getMapKeys_single]
  split
  · rename_i k₀ tag e₁ hA
    have hxA : mapLookup A (.atom "tuple") = some (.tuple ⟨[k₀, tag, e₁]⟩) := by
      cases h : mapLookup A (.atom "tuple") <;> simp_all
    obtain ⟨kA, tA, lA, eA, gA, elA⟩ := tfield_three (fieldC_tuple (sA.fields _ _ hxA)) rfl
    obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj eA
    split
    · rename_i k₁ tag₂ e₂ hB
      have hxB : mapLookup B (.atom "tuple") = some (.tuple ⟨[k₁, tag₂, e₂]⟩) := by
        cases h : mapLookup B (.atom "tuple") <;> simp_all
      obtain ⟨kB, tB, lB, eB, gB, elB⟩ := tfield_three (fieldC_tuple (sB.fields _ _ hxB)) rfl
      obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj eB
      obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      have fallback : ∀ (x : Except Exception Term),
          (∀ c₁ c₂ : Bool, Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A) = .ok (boolAtom c₁) →
            Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B) = .ok (boolAtom c₂) →
            x = .ok (if c₁ && c₂ then u else .atom "nil")) →
          ∃ r, x = .ok r ∧ (r = .atom "nil" ∨ (DE E r ∧ ∀ v : PtD E den tl (FVal E den), denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
        intro x hx
        refine ⟨_, hx c₁ c₂ r₁ r₂, ?_⟩
        cases c₁ <;> cases c₂ <;> simp [hu, usem]
      by_cases G : tB = tA ∧ sa = 1 ∧ sb = 1 ∧ 0 < n
      · obtain ⟨rfl, rfl, rfl, pos⟩ := G
        have sub : Erlang.erlang.«-/2» (.integer n) (.integer 1) = .ok (.integer (n - 1)) := by
          rw [Erlang.erlang.«-/2_integers»]
        have pc : compare n 0 = Ordering.gt := by exact Int.compare_eq_gt.mpr pos
        obtain ⟨r, rr, out⟩ := fuse_elements_sem ef (m := m) (by omega) (n - 1) lA lB [] elA elB (by simp)
        rcases out with rfl | ⟨l, rfl, hl, ll, sl⟩
        · refine ⟨_, ?_, Or.inl rfl⟩
          simp only [Term.list] at rr
          simp [hsa, hsb, Erlang.erlang.«=:=/2», Lynx.Except.andAlso,
            Erlang.erlang.«and/2», Erlang.erlang.«==/2», Erlang.erlang.«>/2», pc, rr, isMember]
        · obtain ⟨k, hk, key⟩ := leaf_new_key tB gA l
          have nf : Term.compareExact (Term.fuel (Term.list l) (.atom "false")) (Term.list l) (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel (Term.list l) (.atom "nil")) (Term.list l) (.atom "nil") ≠ .eq := by
            cases l <;> simp [Term.list]
          refine ⟨_, ?_, Or.inr ⟨fused_de gA hl key,
            fused_sem ef gA elA elB hl hxA hsa hxB hsb fun w => by simpa using sl (tB == "closed") w⟩⟩
          simp [hsa, hsb, Erlang.erlang.«=:=/2», Lynx.Except.andAlso,
            Erlang.erlang.«and/2», Erlang.erlang.«==/2», Erlang.erlang.«>/2», pc, rr, isMember, hk, nf.1, nf.2]
      · refine fallback _ fun c₁ c₂ r₁ r₂ => ?_
        have pc : compare n 0 = Ordering.gt ↔ 0 < n := Int.compare_eq_gt
        by_cases e₁ : tB = tA <;> by_cases e₂ : sa = 1 <;> by_cases e₃ : sb = 1 <;> by_cases e₄ : 0 < n <;>
          simp only [e₁, e₂, e₃, e₄, and_self, not_true_eq_false] at G <;>
          cases c₁ <;> cases c₂ <;>
          simp [hsa, hsb, e₁, e₂, e₃, e₄, pc, r₁, r₂, run, Erlang.erlang.«=:=/2»,
            Lynx.Except.andAlso, Erlang.erlang.«and/2», Erlang.erlang.«==/2»,
            Erlang.erlang.«>/2», isMember, boolAtom]
    · exact second
  · exact second

/-- The step from element types to types over them. -/
theorem ef_step (ef : EF nd E V den tl K) (hnone : E (.map [])) :
    EF nd (DE E) (PtD E den tl (FVal E den)) denD tlD (K + 23) :=
  ef_gen (stepOf ef hnone) fun {_ _} n {_} ha hb ne hm => de_fuse ef hnone n ha hb ne hm

end

end Elixir.STTDescrProofsTest.Nest
