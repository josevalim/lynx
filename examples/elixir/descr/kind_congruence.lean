namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fields and types mean the same up to comparison. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

theorem lookup_rel_cmp {M M' : List (Term × Term)} (h : Term.compare (Term.fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) (q : Term) :
    Option.Rel (fun x y => Term.compare (Term.fuel x y) x y = .eq) (mapLookup M q) (mapLookup M' q) :=
  lookup_of_map_compare_eq M M' h q

theorem isSome_rel {a b : Option Term} (h : Option.Rel (fun x y => Term.compare (Term.fuel x y) x y = .eq) a b) :
    a.isSome = b.isSome := by cases h <;> rfl

theorem tuple2_cmp {a b a' b' : Term} (h : Term.compare (Term.fuel (.tuple #[a, b]) (.tuple #[a', b'])) (.tuple #[a, b]) (.tuple #[a', b']) = .eq) :
    Term.compare (Term.fuel a a') a a' = .eq ∧ Term.compare (Term.fuel b b') b b' = .eq := by
  rw [compare_tuple] at h
  simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
  exact ⟨h.1, h.2.1⟩

theorem map_cmp_shape {X : List (Term × Term)} {b : Term} (h : Term.compare (Term.fuel (.map X) b) (.map X) b = .eq) : ∃ Y, b = .map Y := by
  cases b <;> rw [compare_step] at h <;> simp [Compare.compareStep] at h
  exact ⟨_, rfl⟩

theorem atomF_congr {x x' : Term} (fx : AtomF x) (fx' : AtomF x') (e : Term.compare (Term.fuel x x') x x' = .eq) (q : Term) :
    amemV (some x) q = amemV (some x') q := by
  obtain ⟨⟨p, S, rfl, -⟩, -⟩ := fx
  obtain ⟨⟨p', S', rfl, -⟩, -⟩ := fx'
  obtain ⟨et, es⟩ := tuple2_cmp e
  have tags : p = p' := by cases p <;> cases p' <;> simp_all
  subst tags
  have := isSome_rel (lookup_rel_cmp es q)
  cases p <;> simp [amemV, this]

theorem funF_congr {x x' : Term} (fx : FunF x) (fx' : FunF x') (e : Term.compare (Term.fuel x x') x x' = .eq) (a : Term)
    {ρ : Term → Bool} (resp : Resp ρ) : arityOf x a ρ = arityOf x' a ρ := by
  obtain ⟨p, R, rfl, bR⟩ := fx
  obtain ⟨p', R', rfl, bR'⟩ := fx'
  obtain ⟨et, er⟩ := tuple2_cmp e
  have tags : p = p' := by cases p <;> cases p' <;> simp_all
  subst tags
  rw [arity_tag, arity_tag]
  congr 1
  simp only [evalR]
  have rel := lookup_rel_cmp er a
  cases h : mapLookup R a <;> cases h' : mapLookup R' a <;> rw [h, h'] at rel <;> cases rel
  rename_i v v' cmp
  exact eval_congr_cmp (bR a v h) resp cmp

/-- Fields mean the same up to comparison. -/
theorem fieldC_congr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {name : String} {x x' : Term}
    (fx : FieldC Fn TF LF MF name x) (fx' : FieldC Fn TF LF MF name x') (e : Term.compare (Term.fuel x x') x x' = .eq) (p : Point)
    (ok : PtOkC TV LV MV FV name p) : dn name (some x) p = dn name (some x') p := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨b, rfl, -⟩ := fieldC_bitmap fx
    obtain ⟨b', rfl, -⟩ := fieldC_bitmap fx'
    have : (b : Int) = b' := by simpa using e
    simp [dn_bitmap, this]
  · rw [dn_atom, dn_atom, atomF_congr (fieldC_atom fx) (fieldC_atom fx') e]
  · rw [dn_fun, dn_fun, funF_congr (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fx')) e _ ok.1]
  · exact ks.l.congr (fieldC_list fx) (fieldC_list fx') e p (ok.2.2.1 rfl)
  · exact ks.t.congr (fieldC_tuple fx) (fieldC_tuple fx') e p (ok.2.2.2.1 rfl)
  · exact ks.m.congr (fieldC_map fx) (fieldC_map fx') e p (ok.2.2.2.2.1 rfl)

/-- Types mean the same up to comparison. -/
theorem descr_congr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {A B : List (Term × Term)}
    (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B) (e : Term.compare (Term.fuel (.map A) (.map B)) (.map A) (.map B) = .eq)
    (name : String) (p : Point) (ok : PtOkC TV LV MV FV name p) :
    dn name (mapLookup A (.atom name)) p = dn name (mapLookup B (.atom name)) p := by
  have rel := lookup_rel_cmp e (.atom name)
  cases hA : mapLookup A (.atom name) <;> cases hB : mapLookup B (.atom name) <;> rw [hA, hB] at rel <;> cases rel
  rename_i x y cmp
  exact fieldC_congr ks fc (sA.fields name x hA) (sB.fields name y hB) cmp p ok

end

end Elixir.STTDescrProofsTest.Nest
