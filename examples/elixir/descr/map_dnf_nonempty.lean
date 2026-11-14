namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- `map_bdd_to_dnf_remove_empty/1` lists the non-empty lines of a map BDD of any literals. -/
theorem dnf_lit_map (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {m : Nat}
    (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (MapLitV E) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1» (D m) r =
        .ok (Term.list lines) ∧ (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) ∧
      ∀ w, eval (valM E den w) r = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := by
  obtain ⟨all, run, tl, sl⟩ := dnf_map (den := den) ops dops sem (m := m) hm hS wr (fun t h => h) []
    (.tuple #[.atom "open", .nil]) [] ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩ (by simp)
  have keeps : ∀ L ∈ all, ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) :=
    fun L mL => mline_keep ops dops sem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc)) ∧ (keep L = Bool.true ↔ ∃ w, InMLine den L w) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact Classical.choose_spec (keeps L mL)
  have fold := foldl_det (K := K + 2) "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all (fun x mx a m hm => (hk x mx).1 m a hm) .nil hm
  have e := foldl_filter keep all []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all.filter keep).reverse, ?_, fun L mL => ?_, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1»
    have run' : Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r (.map []) =
        .ok (Term.list all) := by simpa using run
    simp only [run', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all)) =
        Erlang.lists.«foldl/3» (D m) (.function "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[])
          .nil (Term.list all) from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact ⟨tl L mL.1, (hk L mL.1).2.mp mL.2⟩
  · have hp : InPosM den (.tuple #[.atom "open", .nil]) w := ⟨.atom "open", [], rfl, ⟨fun s => by
      simp [FSem, TagSem, mapLookup], fun k i => by simp [TagSem]⟩⟩
    rw [← (by simpa [hp] using sl w : (∃ L ∈ all, InMLine den L w) ↔ eval (valM E den w) r = Bool.true)]
    constructor
    · rintro ⟨L, mL, hL⟩
      exact ⟨L, by simp [mL, (hk L mL).2.mpr ⟨w, hL⟩], hL⟩
    · rintro ⟨L, mL, hL⟩
      simp only [List.mem_reverse, List.mem_filter] at mL
      exact ⟨L, mL.1, hL⟩

end

section
variable {t : Term} {n : Nat}

/-- The pairs `map_to_list/1` lists for the maps of a map type: each key and value of its maps, for every point of the
type of an atom key and every point of the kind of other keys, and only pairs whose value is at a key of its maps. -/
def InnerSem (t : Term) (n : Nat) (b inner : Term) : Prop :=
  (∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true → ∀ s x, w (.atom s) = some x →
    ∀ k, (level t (n + 1)).den (atomT s) k → denD inner (tpt (t := t) (n := n + 1) [k, x])) ∧
  (∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true → ∀ kk i x, w (.dom kk i) = some x →
    ∀ k : (level t (n + 1)).V, ptKind (toPN k) = domKind kk → denD inner (tpt (t := t) (n := n + 1) [k, x])) ∧
  (∀ p : PN t (n + 1), denD inner p → ∃ w' : List (level t (n + 1)).V,
    (∀ Y, denD (.map Y) p ↔ TT t (n + 1) Y w') ∧ ∃ k x, w' = [k, x] ∧
      ∃ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ∧ ∃ κ, w κ = some x)

theorem pairPt_tpt {a b : Term} {k x : (level t (n + 1)).V} (ha : (level t (n + 1)).den a k)
    (hb : (level t (n + 1)).den b x) : PairPt t (n + 1) a b (tpt [k, x]) :=
  ⟨[k, x], fun _ => denD_tpt _, k, x, rfl, ha, hb⟩

end

section
variable {t : Term} {n : Nat}

theorem inner_run {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {b : Term} (fb : MField (level t (n + 1)).E b)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w)
    (sl : ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ↔
      ∃ L ∈ lines, InMLine (level t (n + 1)).den L w) :
    ∃ inner, Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF = .ok inner ∧
      DE (level t (n + 1)).E inner ∧ InnerSem t n b inner := by
  have ef := (level t (n + 1)).ef
  have hl' : ∀ L ∈ lines, MLine (level t (n + 1)).E L := fun L m => (hl L m).1
  rcases mtl_static3 hM fb lines hl with ⟨L, mL, ⟨l, negs, rfl⟩, P, rP, dP, sP⟩ |
    ⟨no, S, inner, run, hS, named, dI, sI⟩
  · refine ⟨P, rP, dP, fun w hw s x hx k hk => (sP _).mpr (pairPt_tpt (ef.den_term k) (ef.den_term x)),
      fun w hw kk i x hx k hk => (sP _).mpr (pairPt_tpt (ef.den_term k) (ef.den_term x)), fun p hp => ?_⟩
    obtain ⟨w', hw', k, x, rfl, -, -⟩ := (sP p).mp hp
    refine ⟨[k, x], hw', k, x, rfl, ?_⟩
    obtain ⟨⟨tag, l', negs', e, -, sl', -⟩, w₀, h₀⟩ := hl _ mL
    obtain ⟨-, rfl, rfl⟩ := tuple3_inj e
    let Mx := ((keyStrs l').map String.length).foldr max 0
    have fr : ∀ c ∈ freshStrs Mx (negs'.length + 1), c ∉ keyStrs l' := fun c mc m => by
      have := le_maxLen _ c m; have := freshStrs_len mc; omega
    obtain ⟨κ, -, w, hw, wκ⟩ := line_witness h₀ ((freshStrs Mx (negs'.length + 1)).map MKey.atom)
      (List.Pairwise.map MKey.atom (fun _ _ ne e => ne (MKey.atom.inj e)) (freshStrs_nodup Mx _)) (by simp [freshStrs_length])
      fun κ mκ => by
        obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
        show FSem (level t (n + 1)).den (.atom "open") l' c (some x)
        unfold FSem; rw [lookup_fresh' (fr c mc)]; exact Or.inl rfl
    exact ⟨w, (sl w).mpr ⟨_, mL, hw⟩, κ, wκ⟩
  · have hnone : ∀ x, ¬(level t (n + 1)).den (.map []) x := fun x h => ef.den_none x h
    refine ⟨inner, run, dI, fun w hw s x hx k hk => ?_, fun w hw kk i x hx k hk => ?_, fun p hp => ?_⟩
    · by_cases hs : (Term.atom s, Term.nil) ∈ S
      · obtain ⟨L, mL, hL⟩ := (sl w).mp hw
        exact (sI _).mpr (Or.inr ⟨s, hs, [k, x], fun _ => denD_tpt _, k, x, rfl, hk, L, mL, w, hL, hx⟩)
      have notR : ∀ a, Term.atom a ∈ S.map Prod.fst → (Term.atom a, Term.nil) ∈ S := fun a h => by
        obtain ⟨e, me, he⟩ := List.mem_map.mp h
        obtain ⟨s', rfl⟩ := hS e me
        simp only [Term.atom.injEq] at he
        subst he
        exact me
      obtain ⟨L, mL, tag, l, negs, rfl, hx'⟩ := unnamed_tag ef (N := []) (R := S.map Prod.fst) lines hl' sl
        (fun s' c _ _ ns nc w => swap_seen ef named (fun h => ns (List.mem_map.mpr ⟨_, h, rfl⟩))
          (fun h => nc (List.mem_map.mpr ⟨_, h, rfl⟩)) w) (by simp [mapLookup]) (fun h => hs (notR s h)) hw hx
      obtain ⟨tag', l', negs', e, g, -, -⟩ := hl' _ mL
      obtain ⟨rfl, -, -⟩ := tuple3_inj e
      rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
      · exact absurd ⟨_, _, rfl⟩ (no _ mL)
      · simp [tagType] at hx'; exact absurd hx' (hnone x)
      · rw [tagType_dom] at hx'
        cases hv : mapLookup dl (.atom "atom") with
        | none => rw [hv] at hx'; exact absurd hx' (hnone x)
        | some v =>
          rw [hv] at hx'
          have dT := (dkdT_run (t := t) (n := n) (d := "atom") (by simp [domainKinds])).2
          have hk' := (den_succ (atomT_de s) (toPN k)).mp hk
          rw [atomT_den] at hk'
          have kd := (den_succ dT.de (toPN k)).mpr (dT.atoms rfl _ hk'.1)
          exact (sI _).mpr (Or.inl ⟨_, mL, dl, l, negs, rfl, "atom", v, dom_mem_of_lookup hv, by simp [domainKinds],
            ⟨x, hx'⟩, pairPt_tpt kd hx'⟩)
    · obtain ⟨L, mL, hL⟩ := (sl w).mp hw
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl' L mL
      have hd := (inMLine_iff.mp hL).1.doms kk i
      rw [hx] at hd
      rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
      · exact absurd ⟨_, _, rfl⟩ (no _ mL)
      · simp [TagSem] at hd
      · rw [tagSem_dom_iff hnone] at hd
        obtain ⟨v, T, ev, hT, hvT⟩ := hd.resolve_left (by simp)
        cases ev
        have dT := (dkdT_run (t := t) (n := n) (domKind_mem kk)).2
        have kd := (den_succ dT.de (toPN k)).mpr (dT.kinds (domKind_ne_atom kk) _ hk)
        exact (sI _).mpr (Or.inl ⟨_, mL, dl, l, negs, rfl, domKind kk, T, dom_mem_of_lookup hT, domKind_mem kk,
          ⟨_, hvT⟩, pairPt_tpt kd hvT⟩)
    · rcases (sI p).mp hp with ⟨L, mL, dl, l, negs, rfl, d, v, mem, md, -, w', hw', k, x, rfl, -, hvx⟩ |
        ⟨s, -, w', hw', k, x, rfl, -, L, mL, w, hL, hws⟩
      · obtain ⟨tag, l', negs', e, g, -, -⟩ := (hl _ mL).1
        obtain ⟨e₁, -, -⟩ := tuple3_inj e
        have dv : DomsV (level t (n + 1)).E dl := by
          rcases g with rfl | rfl | ⟨dl', rfl, dv⟩
          · exact absurd e₁ (fieldsTerm_ne_atom dl "open")
          · exact absurd e₁ (fieldsTerm_ne_atom dl "closed")
          · rwa [fieldsTerm_inj e₁]
        obtain ⟨w, hw, κ, -, wκ⟩ := tag_witness ef (hl _ mL).1 (hl _ mL).2 md
          ⟨fieldsTerm dl, l, negs, rfl, by rw [tagType_dom, dom_lookup_of_mem dv mem]; exact hvx⟩ []
        exact ⟨[k, x], hw', k, x, rfl, w, (sl w).mpr ⟨_, mL, hw⟩, κ, wκ⟩
      · exact ⟨[k, x], hw', k, x, rfl, w, (sl w).mpr ⟨L, mL, hL⟩, .atom s, hws⟩

end

end Elixir.STTDescrProofsTest.Nest
