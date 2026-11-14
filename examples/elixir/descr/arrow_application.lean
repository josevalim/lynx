/-! Application of an intersection of arrows to real argument tuples, and the fast paths of `phi_starter`. -/

namespace Elixir.STTDescrProofsTest.FunSem
variable {V : Type}

/-- Real arguments in an arrow's domain. -/
def InDomR : List (V → Prop) → List V → Prop
  | [], [] => True
  | t :: ts, v :: vs => t v ∧ InDomR ts vs
  | [], _ :: _ => False
  | _ :: _, [] => False

theorem inDom_real : ∀ (ts : List (V → Prop)) (x : List V), InDom ts (x.map some) ↔ InDomR ts x
  | [], [] => Iff.rfl
  | t :: ts, v :: vs => by simp only [List.map, InDom, InDomR, Opt, inDom_real ts vs]
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl

/-- Probes replaced by real values. -/
def fill : List (Option V) → List V → List V
  | o :: os, w :: ws => o.getD w :: fill os ws
  | _, _ => []

theorem fill_args : ∀ (t : List (V → Prop)) (x : List (Option V)) (w : List V), InDomR t w →
    Args (t.map (false, ·)) x → InDomR t (fill x w)
  | [], [], [], _, _ => trivial
  | t :: ts, o :: os, w :: ws, ⟨hw, hws⟩, ⟨ho, hos⟩ => by
    refine ⟨?_, fill_args ts os ws hws hos⟩
    cases o with
    | none => exact hw
    | some v => exact ho
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | [], [], _ :: _, h, _ => h.elim
  | _ :: _, _ :: _, [], h, _ => h.elim

/-- Filling probes keeps a row in every domain it was in only through its real values: domains that contain the
filled row contain the row with probes. -/
theorem inDom_fill : ∀ (us : List (V → Prop)) (x : List (Option V)) (w : List V), x.length = w.length →
    InDom us ((fill x w).map some) → InDom us x
  | [], [], [], _, _ => trivial
  | u :: us, o :: os, w :: ws, len, ⟨ho, hos⟩ => by
    refine ⟨?_, inDom_fill us os ws (by simpa using len) hos⟩
    cases o with
    | none => rfl
    | some v => exact ho
  | [], _ :: _, _ :: _, _, h => by simp [fill, InDom] at h
  | _ :: _, [], _, _, h => by simp [fill, InDom] at h
  | _ :: _, _ :: _, [], len, _ => by simp at len
  | [], [], _ :: _, len, _ => by simp at len
  | [], _ :: _, [], len, _ => by simp at len

theorem inDomR_length : ∀ {t : List (V → Prop)} {x : List V}, InDomR t x → x.length = t.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [inDomR_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- When every argument has a value, rows with probes can be filled with real arguments: no row exists exactly when
no real row exists. -/
theorem noRow_real (P : List (Arrow V)) (t : List (V → Prop)) (s : V → Prop) (w : List V) (hw : InDomR t w) :
    NoRow (t.map (false, ·)) (false, fun v => ¬s v) P ↔
      ∀ x, InDomR t x → ∀ y, (∀ p ∈ P, Allows p (x.map some, y)) → ∃ v, y = some v ∧ s v := by
  constructor
  · intro h x hx y hall
    apply Classical.byContradiction
    intro hn
    refine h (x.map some) y ((inDom_args t _).mp ((inDom_real t x).mpr hx)) ?_ hall
    cases y with
    | none => rfl
    | some v => exact fun hv => hn ⟨v, rfl, hv⟩
  · intro h x y hx hy hall
    have lx : x.length = w.length := by
      rw [inDom_length ((inDom_args t x).mpr hx), inDomR_length hw]
    have hf := fill_args t x w hw hx
    obtain ⟨v, rfl, hv⟩ := h (fill x w) hf y fun p mp hd => hall p mp (inDom_fill p.1 x w lx hd)
    exact hy hv

/-- The results of applying arrows to arguments in `I`, refined by `r`, as `aux_apply/4` builds them: either an
arrow's domain does not cover the remaining arguments, which are applied to the other arrows, or the arrow applies
and refines the result. -/
def App (I : List V → Prop) (r : V → Prop) : List (Arrow V) → V → Prop
  | [] => r
  | (us, s) :: P => fun v => ((∃ x, I x ∧ ¬InDomR us x) ∧ App (fun x => I x ∧ ¬InDomR us x) r P v) ∨
      App I (fun v => r v ∧ s v) P v

theorem app_iff : ∀ (P : List (Arrow V)) (I : List V → Prop) (r : V → Prop), (∃ x, I x) →
    ∀ v, App I r P v ↔ ∃ x, I x ∧ r v ∧ ∀ p ∈ P, InDomR p.1 x → p.2 v
  | [], I, r, ⟨x, hx⟩, v => ⟨fun h => ⟨x, hx, h, by simp⟩, fun ⟨_, _, h, _⟩ => h⟩
  | (us, s) :: P, I, r, ne, v => by
    simp only [App]
    rw [app_iff P I _ ne]
    constructor
    · rintro (⟨ne', h⟩ | ⟨x, hx, ⟨hr, hs⟩, hall⟩)
      · obtain ⟨x, ⟨hx, hd⟩, hr, hall⟩ := (app_iff P _ r ne' v).mp h
        refine ⟨x, hx, hr, fun p mp hp => ?_⟩
        rcases List.mem_cons.mp mp with rfl | mp
        · exact absurd hp hd
        · exact hall p mp hp
      · refine ⟨x, hx, hr, fun p mp hp => ?_⟩
        rcases List.mem_cons.mp mp with rfl | mp
        · exact hs
        · exact hall p mp hp
    · rintro ⟨x, hx, hr, hall⟩
      by_cases hd : InDomR us x
      · exact Or.inr ⟨x, hx, ⟨hr, hall (us, s) (by simp) hd⟩, fun p mp => hall p (by simp [mp])⟩
      · exact Or.inl ⟨⟨x, hx, hd⟩, (app_iff P _ r ⟨x, hx, hd⟩ v).mpr
          ⟨x, ⟨hx, hd⟩, hr, fun p mp => hall p (by simp [mp])⟩⟩

/-- With non-empty arguments covered by the domains of the positive arrows, a negative arrow contains them exactly
when applying them to its arguments gives results in its return. -/
theorem noRow_app (P : List (Arrow V)) (t : List (V → Prop)) (s : V → Prop) (w : List V) (hw : InDomR t w)
    (cover : ∀ x, InDomR t x → ∃ p ∈ P, InDomR p.1 x) :
    NoRow (t.map (false, ·)) (false, fun v => ¬s v) P ↔ ∀ v, App (InDomR t) (fun _ => True) P v → s v := by
  rw [noRow_real P t s w hw]
  constructor
  · intro h v hv
    obtain ⟨x, hx, -, hall⟩ := (app_iff P _ _ ⟨w, hw⟩ v).mp hv
    obtain ⟨v', e, hs⟩ := h x hx (some v) fun p mp hd => ⟨v, rfl, hall p mp ((inDom_real p.1 x).mp hd)⟩
    cases e; exact hs
  · intro h x hx y hall
    obtain ⟨p, mp, hp⟩ := cover x hx
    obtain ⟨v, rfl, -⟩ := hall p mp ((inDom_real p.1 x).mpr hp)
    refine ⟨v, rfl, h v ((app_iff P _ _ ⟨w, hw⟩ v).mpr ⟨x, hx, trivial, fun q mq hq => ?_⟩)⟩
    obtain ⟨v', e, hv'⟩ := hall q mq ((inDom_real q.1 x).mpr hq)
    cases e; exact hv'

/-- With pairwise disjoint domains, the results are the returns of the arrows whose domain meets the arguments. -/
theorem app_disjoint (P : List (Arrow V)) (I : List V → Prop) (ne : ∃ x, I x)
    (disj : ∀ i j (hi : i < P.length) (hj : j < P.length), i ≠ j → ∀ x, InDomR P[i].1 x → ¬InDomR P[j].1 x)
    (cover : ∀ x, I x → ∃ p ∈ P, InDomR p.1 x) (s : V → Prop) :
    (∀ v, App I (fun _ => True) P v → s v) ↔ ∀ p ∈ P, (∃ x, I x ∧ InDomR p.1 x) → ∀ v, p.2 v → s v := by
  constructor
  · intro h p mp ⟨x, hx, hd⟩ v hv
    refine h v ((app_iff P I _ ne v).mpr ⟨x, hx, trivial, fun q mq hq => ?_⟩)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem mq
    by_cases e : i = j
    · subst e; exact hv
    · exact absurd hq (disj i j hi hj e x hd)
  · intro h v hv
    obtain ⟨x, hx, -, hall⟩ := (app_iff P I _ ne v).mp hv
    obtain ⟨p, mp, hp⟩ := cover x hx
    exact h p mp ⟨x, hx, hp⟩ v (hall p mp hp)

end Elixir.STTDescrProofsTest.FunSem
