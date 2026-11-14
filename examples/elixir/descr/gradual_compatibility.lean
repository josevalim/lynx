namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Compatibility of gradual types whose function types are the top one. -/

section
variable {L : Level}

/-- Static types whose function types are function types of element types are element types of the next level. -/
theorem de_of_tc {a : Term} (ha : TCF L a)
    (top : ∀ X x, a = .map X → mapLookup X (.atom "fun") = some x → FunA L.E x) : DE L.E a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨X, rfl, sX.keys, fun name x h => ?_⟩
    rcases sX.fields name x h with h' | h' | ⟨e, -⟩ | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · subst e; exact Or.inr (Or.inr (Or.inl ⟨rfl, top X x rfl h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))

theorem de_tc {a : Term} (ha : DE L.E a) : TC L a := ha

/-- The shapes of gradual types: the top type, static maps, maps whose dynamic part is the top type, and maps whose
dynamic part is a static map. -/
theorem GC.cases {a : Term} (ha : GC L a) :
    a = .atom "term" ∨ (∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = none) ∨
      (∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = some (.atom "term")) ∨
      ∃ X Y, a = .map X ∧ mapLookup X (.atom "dynamic") = some (.map Y) ∧ mapLookup Y (.atom "dynamic") = none := by
  rcases ha with (rfl | ⟨X, rfl, sX⟩) | ⟨X, Dy, rfl, hD, tD, -, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨X, rfl, sX.static⟩)
  · rcases tD with rfl | ⟨Y, rfl, sY⟩
    · exact Or.inr (Or.inr (Or.inl ⟨X, rfl, hD⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨X, Y, rfl, hD, sY.static⟩))

/-- Emptiness of a gradual type checks its dynamic part. -/
theorem empty_upper (d : Dispatcher) {a : Term} (ha : GC L a) :
    Elixir.Module.Types.Descr.«empty?/1» d a = Elixir.Module.Types.Descr.«empty?/1» d (upper a) := by
  rcases ha.cases with rfl | ⟨X, rfl, h⟩ | ⟨X, rfl, h⟩ | ⟨X, Y, rfl, h, hY⟩
  · rfl
  · simp [upper, h]
  · simp only [upper, h, Option.getD_some, empty_map_seen]
    rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, h, Elixir.Module.Types.Descr.«empty?/1»]
  · simp only [upper, h, Option.getD_some, empty_map_seen]
    conv => lhs; rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    conv => rhs; rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, h, hY]

/-- Disjointness of gradual types checks their dynamic parts. -/
theorem disj_upper (d : Dispatcher) {a b : Term} (ha : GC L a) (hb : GC L b) :
    Elixir.Module.Types.Descr.«disjoint?/2» d a b = Elixir.Module.Types.Descr.«disjoint?/2» d (upper a) (upper b) := by
  have ea := empty_upper d ha
  have eb := empty_upper d hb
  rcases ha.cases with rfl | ⟨X, rfl, h⟩ | ⟨X, rfl, h⟩ | ⟨X, X', rfl, h, h'⟩ <;>
    rcases hb.cases with rfl | ⟨Y, rfl, k⟩ | ⟨Y, rfl, k⟩ | ⟨Y, Y', rfl, k, k'⟩ <;>
    simp only [upper, Option.getD_some, Option.getD_none, *] at ea eb ⊢ <;>
    unfold Elixir.Module.Types.Descr.«disjoint?/2» <;>
    simp [getMapKeys_single, upper_term, *]

/-- On static types, `subtype_static?/2` answers as `subtype?/2`. -/
theorem sstatic_sub {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m) :
    Elixir.Module.Types.Descr.«subtype_static?/2» (D m) a b = Elixir.Module.Types.Descr.«subtype?/2» (D m) a b := by
  by_cases incl : ∀ v : TP L, denD a v → denD b v
  · rw [sstatic_complete ha hb hm incl, tc_sub ha hb hm incl]
  obtain ⟨T, term, sT, -, all⟩ := termT L
  have static : ∀ {X : List (Term × Term)}, DC L X → ∀ {Y : List (Term × Term)}, DC L Y →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) =
        Elixir.Module.Types.Descr.«subtype_static?/2» (D m) (.map X) (.map Y) := by
    intro X sX Y sY
    unfold Elixir.Module.Types.Descr.«subtype?/2»
    simp [unfold_map, Erlang.erlang.«is_map_key/2», sX.static, sY.static, any_key,
      Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact absurd (fun v _ => denD_term v) incl
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [subtype_term_l term, static sT sB]
    have ne : compareExact (fuel (.map B) (.map T)) (.map B) (.map T) ≠ .eq := fun e => incl fun v _ =>
      (tc_congr (Or.inr ⟨B, rfl, sB⟩) (Or.inr ⟨T, rfl, sT⟩) (compare_eq_of_compareExact_eq _ _ e) v).mpr (all v)
    unfold Elixir.Module.Types.Descr.«subtype_static?/2»
    simp [Erlang.erlang.«=:=/2», ne, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
    conv => lhs; rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    conv => rhs; rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, sT.static, sB.static, term]
    split <;> rfl
  · exact (static sA sB).symm

end

/-- Static types whose function types `arrows?/2` accepts, arrows between nested types, are element types of the
next level. -/
theorem arrows_de {t : Term} {n : Nat} {b : Term} (hb : TCF (level t n) b)
    (h : «arrows?/2» b (.tuple #[.integer n, t]) = .ok (.atom "true")) : DE (level t n).E b := by
  refine de_of_tc hb fun X x e hx => ?_
  subst e
  unfold «arrows?/2» at h
  simp only [getMapKeys_single, hx] at h
  obtain ⟨hn, hk⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
  have ff : FField (Nest t n) x := by
    rcases nested_field_spec (nested_spec t n) _ _ hn with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, ff⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    all_goals first | exact ff | simp at e
  have fq := keyed_fields_spec (keyed_spec n) Bool.true [(.atom "fun", x)] (by simpa [Term.list, boolAtom] using hk)
    _ (List.mem_singleton_self _)
  rw [← level_nd t n] at ff
  exact funA_of (nest_level t n) (by rw [level_nd] at ff; exact ff) (fq.1 rfl rfl)

/-- `compatible?/2` checks the dynamic parts when the static part of the left type is empty, and inclusion of the
static part otherwise. -/
theorem compat_run (d : Dispatcher) {l r : Term} (hl : l = .atom "term" ∨ ∃ X, l = .map X)
    (hr : UB r) {e s j : Bool}
    (eE : Elixir.Module.Types.Descr.«empty?/1» d (lower l) = .ok (boolAtom e))
    (eS : Elixir.Module.Types.Descr.«subtype_static?/2» d (lower l) (upper r) = .ok (boolAtom s))
    (eJ : Elixir.Module.Types.Descr.«disjoint?/2» d (upper l) (upper r) = .ok (boolAtom j)) :
    Elixir.Module.Types.Descr.«compatible?/2» d l r = .ok (boolAtom (if e then !j else s)) := by
  have finish : ∀ {lo up up' : Term}, Elixir.Module.Types.Descr.«empty?/1» d lo = .ok (boolAtom e) →
      Elixir.Module.Types.Descr.«subtype_static?/2» d lo up' = .ok (boolAtom s) →
      Elixir.Module.Types.Descr.«disjoint?/2» d up up' = .ok (boolAtom j) →
      (do
        let x ← Elixir.Module.Types.Descr.«empty?/1» d lo
        Lynx.Except.guard (.ok (x.isMember [.atom "false", .atom "nil"]))
          (fun _ => Elixir.Module.Types.Descr.«subtype_static?/2» d lo up')
          fun _ => do
            let y ← Elixir.Module.Types.Descr.«disjoint?/2» d up up'
            Erlang.erlang.«not/1» y) = .ok (boolAtom (if e then !j else s)) := by
    intro lo up up' h₁ h₂ h₃
    cases e <;> cases j <;> simp [h₁, h₂, h₃, boolAtom, isMember, Erlang.erlang.«not/1»]
  rcases hl with rfl | ⟨X, rfl⟩ <;> rcases hr with rfl | ⟨Y, rfl, hd⟩
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    simp
    exact finish eE eS eJ
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    cases hY : mapLookup Y (.atom "dynamic") with
    | none =>
      simp only [upper, hY, Option.getD_none] at eS eJ
      simp [getMapKeys_single, hY]
      exact finish eE eS eJ
    | some Dy =>
      simp only [upper, hY, Option.getD_some] at eS eJ
      rcases hd Dy hY with rfl | ⟨Z, rfl⟩ <;> simp [getMapKeys_single, hY] <;> exact finish eE eS eJ
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    simp [unfold_map, pop_dyn]
    exact finish eE eS eJ
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    cases hY : mapLookup Y (.atom "dynamic") with
    | none =>
      simp only [upper, hY, Option.getD_none] at eS eJ
      simp [unfold_map, pop_dyn, getMapKeys_single, hY]
      exact finish eE eS eJ
    | some Dy =>
      simp only [upper, hY, Option.getD_some] at eS eJ
      rcases hd Dy hY with rfl | ⟨Z, rfl⟩ <;> simp [unfold_map, pop_dyn, getMapKeys_single, hY] <;>
        exact finish eE eS eJ

/-- `compatible?/2` checks that the static part of the left type is included in the dynamic part of the right one and
that the two meet, as the law states it. -/
theorem gd_compatible {t : Term} {n : Nat} {l r : Term} (gl : GC (level t n) l) (gr : GC (level t n) r) (ll : DE (level t n).E (lower l))
    (ul : DE (level t n).E (upper l)) (ur : DE (level t n).E (upper r)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«compatible?/2» (D m) l r = .ok (boolAtom b) ∧
      Lynx.Except.andAlso (Elixir.Module.Types.Descr.«subtype?/2» (D m) (lower l) (upper r))
        (do
          let j ← Elixir.Module.Types.Descr.«disjoint?/2» (D m) l r
          Erlang.erlang.«not/1» j) true = .ok (boolAtom b) := by
  have ef3 : EF (level t n).nd (DE (level t n).E)
      (PtD (level t n).E (level t n).den (level t n).tl (FVal (level t n).E (level t n).den)) denD tlD
      ((level t n).K + 23) := ef_step (level t n).ef (level t n).none
  let toTP : PtD (level t n).E (level t n).den (level t n).tl (FVal (level t n).E (level t n).den) → TP (level t n) :=
    fun v => v
  obtain ⟨bE, rE, semE⟩ := ef3.empty [] ll
  replace semE := semE (lh (lower l) + 1) (by omega) (safeN_nil _)
  obtain ⟨s, rS, semS⟩ := ef3.sub ll ur
  obtain ⟨dj, rJ, semJ⟩ := ef3.disj ul ur
  have tl := de_tc ll
  have tr := de_tc ur
  have eS : Elixir.Module.Types.Descr.«subtype_static?/2» (D m) (lower l) (upper r) = .ok (boolAtom s) := by
    rw [sstatic_sub tl tr (by omega), rS m hm]
  have eE : Elixir.Module.Types.Descr.«empty?/1» (D m) (lower l) = .ok (boolAtom bE) := by
    rcases tl with e | ⟨X, e, -⟩ <;> rw [e] at rE semE ⊢
    · have : bE = Bool.false := by
        cases bE
        · rfl
        · exact absurd (denD_term ptWit) ((semE.mp rfl) ptWit)
      subst this; rfl
    · rw [empty_map_seen]; exact rE m hm
  have eJ : Elixir.Module.Types.Descr.«disjoint?/2» (D m) l r = .ok (boolAtom dj) := by
    rw [disj_upper (D m) gl gr]; exact rJ m hm
  have eJ' : Elixir.Module.Types.Descr.«disjoint?/2» (D m) (upper l) (upper r) = .ok (boolAtom dj) := rJ m hm
  have hc := compat_run (D m) gl.shape gr.ub eE eS eJ'
  rw [hc]
  simp only [eJ, rS m hm, Lynx.Except.ok_bind]
  cases bE
  · -- The static part is not empty: it must be included and then the types meet.
    refine ⟨s, by simp, ?_⟩
    cases s
    · simp [boolAtom, Lynx.Except.andAlso]
    · have meet : dj = Bool.false := by
        cases dj
        · rfl
        · obtain ⟨v, hv⟩ : ∃ v, denD (lower l) v := by
            apply Classical.byContradiction; intro h
            exact absurd (semE.mpr fun v hv => h ⟨v, hv⟩) (by simp)
          exact (semJ rfl v (gl.inv (toTP v) ((denD_lower l (toTP v)).mp hv)) (semS rfl v hv)).elim
      subst meet
      simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  · -- The static part is empty, so it is included.
    have sub : s = Bool.true := by
      have := ef3.subc ll ur (fun v hv => absurd hv ((semE.mp rfl) v)) m hm
      rw [rS m hm] at this
      cases s <;> simp_all [boolAtom]
    subst sub
    refine ⟨!dj, by simp, ?_⟩
    cases dj <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]

end Elixir.STTDescrProofsTest.Nest
