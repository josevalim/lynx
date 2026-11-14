namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types as the function checks use them, under seen sets above them. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem EF.den_none (ef : EF nd E V den tl K) (v : V) : ¬den (.map []) v := by
  obtain ⟨b, run, ex⟩ := ef.empty [] ef.none
  have r := run K (Nat.le_refl _)
  rw [empty_none_seen] at r
  have : b = Bool.true := by cases b <;> simp_all [boolAtom]
  subst this
  exact (ex 1 (by rw [lh_nil_map]; omega) (safeN_nil _)).mp rfl v

theorem EF.den_none' (ef : EF nd E V den tl K) {a : Term} (ha : E a) (none : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) (v : V) :
    ¬den a v := fun d => ef.den_none v (ef.resp ef.none ha (Lynx.Term.compare_eq_symm none) d)

theorem EF.congr (ef : EF nd E V den tl K) {N : Nat} : DenCongr (EB E N) den := by
  intro a a' ha ha' e
  funext v
  exact propext ⟨fun d => ef.resp ha'.1 ha.1 (Lynx.Term.compare_eq_symm e) d, fun d => ef.resp ha.1 ha'.1 e d⟩

/-- Element types below the height `H` are element types of the function checks under seen sets above them, given
complete subtyping. -/
theorem felem (ef : EF nd E V den tl K)
    (subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true"))
    {H : Nat} (one : 1 ≤ H) {S : List (Term × Term)} (hS : SafeN H S) : FunElem (EB E H) den K (.map S) where
  phi := {
    inter := fun ha hb => let ⟨c, hc, run, sem, h⟩ := ef.inter ha.1 hb.1; ⟨c, ⟨hc, h H ha.2 hb.2⟩, run, sem⟩
    diff := fun ha hb => let ⟨c, hc, run, sem, h⟩ := ef.diff ha.1 hb.1; ⟨c, ⟨hc, h H ha.2 hb.2⟩, run, sem⟩
    empty := fun {a} ha m hm => by
      obtain ⟨b, run, ex⟩ := ef.empty S ha.1
      rw [run m hm]
      congr 2
      cases b
      · symm; exact Bool.eq_false_iff.mpr fun h => by
          have := (ex H ha.2 hS).mpr ((isEmpty_iff den a).mp h); cases this
      · symm; exact (isEmpty_iff den a).mpr ((ex H ha.2 hS).mp rfl)
    congr := ef.congr }
  union := fun ha hb => let ⟨c, hc, run, sem, h⟩ := ef.union ha.1 hb.1; ⟨c, ⟨hc, h H ha.2 hb.2⟩, run, sem⟩
  neg := fun {a} ha => by
    rcases ef.static ha.1 with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩
    · refine ⟨.map [], ⟨ef.none, by rw [lh_nil_map]; omega⟩, fun m _ => by
        unfold Elixir.Module.Types.Descr.«bare_negation/1»; rfl, fun v => ?_⟩
      exact ⟨fun d => absurd d (ef.den_none v), fun d => absurd (ef.den_term v) d⟩
    all_goals
      obtain ⟨c, hc, run, sem, h⟩ := ef.diff ef.term ha.1
      exact ⟨c, ⟨hc, h H (by simp [lh]; omega) ha.2⟩, fun m hm => by
        unfold Elixir.Module.Types.Descr.«bare_negation/1»; exact run m hm,
        fun v => by rw [sem]; exact ⟨fun h => h.2, fun h => ⟨ef.den_term v, h⟩⟩⟩
  sub := fun {a b} ha hb m hm => by
    obtain ⟨s, run, sound⟩ := ef.sub ha.1 hb.1
    rw [run m hm]
    congr 2
    cases s
    · symm; refine bp_false.mpr fun incl => ?_
      have := (run m hm).symm.trans (subc ha.1 hb.1 incl m hm)
      simp [boolAtom] at this
    · symm; exact bp_true.mpr (sound rfl)
  disj := fun ha hb => let ⟨s, run, sound⟩ := ef.disj ha.1 hb.1; ⟨s, run, sound⟩
  term := ⟨⟨ef.term, by simp [lh]; omega⟩, ef.den_term⟩
  none := ⟨⟨ef.none, by rw [lh_nil_map]; omega⟩, ef.den_none⟩

end

/-! Domains of arrows of element types: tuple types of them, standing for the lists of values they hold. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Domains of arrows of element types below the height `H`: tuple types of the next level, no higher than `H`. -/
def DomA (E : Term → Prop) (H : Nat) (t : Term) : Prop :=
  TupC (EB E H) t ∧ ∃ X, t = .map X ∧ DescrC FunTop (TField E) (LF E) (MField E) X ∧ lh (.map X) ≤ H

/-- The lists of values a domain holds. -/
def ddenA (E : Term → Prop) (den : Term → V → Prop) (t : Term) (x : List V) : Prop :=
  ∃ X, t = .map X ∧ dn "tuple" (mapLookup X (.atom "tuple")) (0, .nil, valT E den x) = Bool.true

theorem inT_dom : ∀ (l : List Term) (x : List V), InT den Bool.true l x ↔ FunSem.InDomR (l.map den) x
  | [], [] => by simp [InT, FunSem.InDomR]
  | [], _ :: _ => by simp [InT, FunSem.InDomR]
  | _ :: _, [] => by simp [InT, FunSem.InDomR]
  | e :: l, v :: x => by simp only [InT, List.map_cons, FunSem.InDomR, inT_dom l x]

/-- The domain of arguments: the closed tuple of them, keyed as Descr keys closed literals. -/
theorem args_domain_key (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", Term.list l])]) ∧
    KeyOk (.tuple #[.integer k, .atom "closed", Term.list l]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf, key⟩ := leaf_new_key "closed" (Or.inr rfl) l
  refine ⟨k, ?_, key⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  unfold Elixir.Module.Types.Descr.«args_to_domain/1»
  cases l <;> simp_all [Erlang.erlang.«is_list/1», Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2», Term.list]

theorem lh_closed_le {k : Int} {l : List Term} {H : Nat} (one : 1 ≤ H) (hl : ∀ e ∈ l, lh e < H) :
    lh (.tuple #[.integer k, .atom "closed", Term.list l]) ≤ H := by
  by_cases ne : ExpEls "closed" l
  · obtain ⟨-, r, a, b, rfl⟩ := ne
    have : lh (.tuple ⟨[.reference r, .map a, b]⟩) = 1 := by rw [lh]
    simp only [Term.list]
    rw [show (#[Term.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple #[.reference r, .map a, b]) .nil)] :
      Array Term) = ⟨[Term.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩
      from rfl, lh_nodeLit, this]
    exact one
  · rw [lh_lit (Or.inr rfl) (by simp) ne]
    have := lh_list_le l (M := H - 1) fun e me => by have := hl e me; omega
    omega

theorem tupC_keys {H : Nat} {X : List (Term × Term)} (h : TupC (EB E H) (.map X)) {name : String} (ne : name ≠ "tuple") :
    mapLookup X (.atom name) = Option.none := by
  obtain ⟨X', e, -, keys⟩ := h
  simp only [Term.map.injEq] at e
  subst e
  cases hx : mapLookup X (.atom name) with
  | none => rfl
  | some x =>
    have := keys _ (by rw [hx]; rfl)
    simp only [Term.atom.injEq] at this
    exact absurd this ne

/-- Emptiness of domains: exact under seen sets above them, or keyed by an arity, as high. -/
theorem domA_empty (ef : EF nd E V den tl K) {H : Nat} {a : Term} (ha : DomA E H a) (S : List (Term × Term))
    (hS : SafeT (H + 1) S) {m : Nat} (hm : K + 1 ≤ m) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom (bp (∀ x, ¬ddenA E den a x))) := by
  obtain ⟨tc, X, rfl, sX, lX⟩ := ha
  by_cases ne : X = []
  · subst ne
    rw [empty_none_seen]
    have : bp (∀ x, ¬ddenA E den (.map []) x) = Bool.true := bp_true.mpr fun x ⟨Y, e, d⟩ => by
      simp only [Term.map.injEq] at e; subst e; simp [mapLookup, dn_none] at d
    rw [this]; rfl
  obtain ⟨xt, hxt⟩ : ∃ xt, mapLookup X (.atom "tuple") = some xt := by
    cases X with
    | nil => exact absurd rfl ne
    | cons e rest =>
      obtain ⟨X', eX, -, keys⟩ := tc
      simp only [Term.map.injEq] at eX
      have h1 : (mapLookup (e :: rest) e.1).isSome := by simp [mapLookup]
      have q := keys e.1 (by rw [← eX]; exact h1)
      rw [q] at h1
      exact Option.isSome_iff_exists.mp h1
  have fx : TField E xt := fieldC_tuple (sX.fields "tuple" xt hxt)
  obtain ⟨bt, run, ex⟩ := tuple_empty_exact ef fx S
  have lt : lh xt < H + 1 := by have := lh_field_le hxt; omega
  have r := descr_empty_run (D m) (S := .map S) (bt := bt) (bm := Bool.true) (bl := Bool.true) (bf := Bool.true)
    sX.static ne (fun x h => by rw [hxt] at h; cases h; exact run m hm)
    (fun x h => by rw [tupC_keys (name := "map") tc (by decide)] at h; cases h)
    (fun x h => by rw [tupC_keys (name := "list") tc (by decide)] at h; cases h)
    (fun x h => by rw [tupC_keys (name := "fun") tc (by decide)] at h; cases h)
  rw [r, tupC_keys (name := "atom") tc (by decide), tupC_keys (name := "bitmap") tc (by decide),
    tupC_keys (name := "map") tc (by decide), tupC_keys (name := "list") tc (by decide),
    tupC_keys (name := "fun") tc (by decide), hxt]
  simp only [Option.isSome_none, Bool.not_false, Bool.true_and, Option.isNone_some, Bool.false_or, Option.isNone_none,
    Bool.true_or, Bool.and_true]
  congr 2
  have sem : (∀ x, ¬ddenA E den (.map X) x) ↔ ∀ v, denTF E den xt v = Bool.false := by
    constructor
    · intro h v
      cases hv : denTF E den xt v
      · rfl
      · exact absurd ⟨X, rfl, by rw [hxt, dn_tupleT rfl]; exact hv⟩ (h v)
    · rintro h x ⟨Y, e, d⟩
      simp only [Term.map.injEq] at e; subst e
      rw [hxt, dn_tupleT rfl, h x] at d; cases d
  cases bt
  · symm; refine bp_false.mpr fun h => ?_
    have := (ex (H + 1) lt hS).mpr (sem.mp h); cases this
  · symm; exact bp_true.mpr (sem.mpr ((ex (H + 1) lt hS).mp rfl))

theorem safeT_nil (N : Nat) : SafeT N [] := fun _ h => by simp at h

/-- Points of tuple fields at the values `x`. -/
theorem ptTup (ef : EF nd E V den tl K) (x : List V) :
    PtOkC (ValT E den) (ValLN E den tl) (ValMN E den) FVT "tuple" (0, .nil, valT E den x) :=
  ptOk_tuple (kinds ef) ⟨x, rfl⟩

/-- Domains of arrows of element types below the height `H` are domains of the function checks under seen sets
above them, or keyed by an arity, as high. -/
theorem fdom (ef : EF nd E V den tl K) {H : Nat} (one : 1 ≤ H) {S : List (Term × Term)} (hS : SafeT (H + 1) S) :
    FunDom (DomA E H) (EB E H) den (ddenA E den) (K + 6) (.map S) := by
  have hnone : EB E H (.map []) := ⟨ef.none, by rw [lh_nil_map]; omega⟩
  have dm := domOk (ef.ops H (by omega)) (ef.dops H) (ef.funB H) hnone (ef.tailB H)
  have sem2 : ∀ {X Y : List (Term × Term)} {U : List (Term × Term)} (f : Bool → Bool → Bool),
      (∀ name p, PtOkC (ValT E den) (ValLN E den tl) (ValMN E den) FVT name p →
        dn name (mapLookup U (.atom name)) p = f (dn name (mapLookup X (.atom name)) p) (dn name (mapLookup Y (.atom name)) p)) →
      ∀ x, ddenA E den (.map U) x ↔ f (dn "tuple" (mapLookup X (.atom "tuple")) (0, .nil, valT E den x))
        (dn "tuple" (mapLookup Y (.atom "tuple")) (0, .nil, valT E den x)) = Bool.true := by
    intro X Y U f sem x
    constructor
    · rintro ⟨U', e, d⟩
      simp only [Term.map.injEq] at e; subst e
      rw [← sem _ _ (ptTup ef x)]; exact d
    · intro h; exact ⟨U, rfl, by rw [sem _ _ (ptTup ef x)]; exact h⟩
  have ddenM : ∀ {X : List (Term × Term)} (x : List V), ddenA E den (.map X) x ↔
      dn "tuple" (mapLookup X (.atom "tuple")) (0, .nil, valT E den x) = Bool.true := by
    intro X x
    constructor
    · rintro ⟨U', e, d⟩; simp only [Term.map.injEq] at e; subst e; exact d
    · intro h; exact ⟨X, rfl, h⟩
  refine ⟨fun l hl => ?_, ⟨⟨dm.none, [], rfl, descrC_nil, by rw [lh_nil_map]; omega⟩, fun x ⟨Y, e, d⟩ => ?_⟩,
    fun ha => dm.isMap ha.1, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_,
    fun ha m hm => domA_empty ef ha [] (safeT_nil _) (by omega), fun ha m hm => domA_empty ef ha S hS (by omega)⟩
  · obtain ⟨k, run, key⟩ := args_domain_key l fun e me => ef.static (hl e me).1
    obtain ⟨t, tc, run'⟩ := dm.dom l hl
    rw [run] at run'; cases run'
    have look : ∀ q, mapLookup [(Term.atom "tuple", Term.tuple #[.integer k, .atom "closed", Term.list l])] q =
        if compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq then some (.tuple #[.integer k, .atom "closed", Term.list l])
        else Option.none := by
      intro q; by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq <;> simp [mapLookup, e]
    have lit : TLit E (.tuple #[.integer k, .atom "closed", Term.list l]) :=
      ⟨⟨⟨k, "closed", l, rfl, Or.inr rfl, fun e me => (hl e me).1⟩, fun ⟨_, e⟩ => by simp at e⟩, key⟩
    refine ⟨_, ⟨tc, _, rfl, ⟨fun q h => ?_, fun name w h => ?_⟩, ?_⟩, run, fun x => ?_⟩
    · rw [look] at h; split at h
      · rename_i e; exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
      · simp at h
    · rw [look] at h; split at h
      · rename_i e
        simp only [atom_compareExact_eq, Term.atom.injEq] at e
        subst e
        simp at h; subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Bdd.leaf_iff.mpr lit)⟩))))
      · simp at h
    · refine lh_map_le.mpr fun e me => ?_
      simp only [mapEntries_singleton, List.mem_singleton] at me
      subst me
      exact lh_closed_le one fun e me => (hl e me).2
    · rw [ddenM, show mapLookup [(Term.atom "tuple", Term.tuple #[.integer k, .atom "closed", Term.list l])] (.atom "tuple") =
          some (.tuple #[.integer k, .atom "closed", Term.list l]) by simp [mapLookup], dn_tupleT rfl,
        denTF_leaf ef (Or.inr rfl) (fun e me => (hl e me).1), vT_lit ef (Or.inr rfl) (fun e me => (hl e me).1)]
      exact inT_dom l x
  · simp only [Term.map.injEq] at e; subst e; simp [mapLookup, dn_none] at d
  · obtain ⟨c, tc, run⟩ := dm.union ha.1 hb.1
    obtain ⟨-, A, rfl, sA, lA⟩ := ha
    obtain ⟨-, B, rfl, sB, lB⟩ := hb
    obtain ⟨U, run', sU, sem, le⟩ := descr_union (kinds ef) (fcOf K) (m := K + 5) (by omega) sA sB
    rw [run (K + 6) (by omega)] at run'; cases run'
    refine ⟨_, ⟨tc, U, rfl, sU, by have := le trivial; omega⟩, fun m hm => run m (by omega), fun x => ?_⟩
    rw [sem2 (· || ·) sem x, ddenM, ddenM, Bool.or_eq_true]
  · obtain ⟨c, tc, run⟩ := dm.inter ha.1 hb.1
    obtain ⟨-, A, rfl, sA, lA⟩ := ha
    obtain ⟨-, B, rfl, sB, lB⟩ := hb
    obtain ⟨U, run', sU, sem, le⟩ := descr_inter (kinds ef) (fcOf K) (m := K + 5) (by omega) sA sB
    rw [run (K + 6) (by omega)] at run'; cases run'
    refine ⟨_, ⟨tc, U, rfl, sU, by have := le trivial; omega⟩, fun m hm => run m (by omega), fun x => ?_⟩
    rw [sem2 (· && ·) sem x, ddenM, ddenM, Bool.and_eq_true]
  · obtain ⟨c, tc, run⟩ := dm.diff ha.1 hb.1
    obtain ⟨-, A, rfl, sA, lA⟩ := ha
    obtain ⟨-, B, rfl, sB, lB⟩ := hb
    obtain ⟨U, run', sU, sem, le⟩ := descr_diff (kinds ef) (fcOf K) (m := K + 4) (by omega) sA sB
    rw [run (K + 6) (by omega)] at run'; cases run'
    refine ⟨_, ⟨tc, U, rfl, sU, by have := le trivial; omega⟩, fun m hm => run m (by omega), fun x => ?_⟩
    rw [sem2 (fun a b => a && !b) sem x, ddenM, ddenM]
    simp

end

/-! Emptiness of function types of element types: exact on functions, under seen sets above them. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem FunElem.mono {E : Term → Prop} {den : Term → V → Prop} {K K' : Nat} {seen : Term}
    (fe : FunElem E den K seen) (le : K ≤ K') : FunElem E den K' seen where
  phi := {
    inter := fun ha hb => let ⟨c, hc, run, sem⟩ := fe.phi.inter ha hb; ⟨c, hc, fun m hm => run m (by omega), sem⟩
    diff := fun ha hb => let ⟨c, hc, run, sem⟩ := fe.phi.diff ha hb; ⟨c, hc, fun m hm => run m (by omega), sem⟩
    empty := fun ha m hm => fe.phi.empty ha m (by omega)
    congr := fe.phi.congr }
  union := fun ha hb => let ⟨c, hc, run, sem⟩ := fe.union ha hb; ⟨c, hc, fun m hm => run m (by omega), sem⟩
  neg := fun ha => let ⟨c, hc, run, sem⟩ := fe.neg ha; ⟨c, hc, fun m hm => run m (by omega), sem⟩
  sub := fun ha hb m hm => fe.sub ha hb m (by omega)
  disj := fun ha hb => let ⟨s, run, sem⟩ := fe.disj ha hb; ⟨s, fun m hm => run m (by omega), sem⟩
  term := fe.term
  none := fe.none

theorem EF.congrE (ef : EF nd E V den tl K) : DenCongr E den := by
  intro a a' ha ha' e
  funext v
  exact propext ⟨fun d => ef.resp ha' ha (Lynx.Term.compare_eq_symm e) d, fun d => ef.resp ha ha' e d⟩

theorem fresh_arities : ∀ (R : List (Term × Term)), ∃ n : Nat, ∀ m, n ≤ m → mapLookup R (.integer m) = Option.none
  | [] => ⟨0, fun _ _ => rfl⟩
  | e :: R => by
    obtain ⟨n, hn⟩ := fresh_arities R
    obtain ⟨j, hj⟩ : ∃ j : Nat, ∀ m : Nat, j ≤ m → e.1 ≠ .integer m := by
      cases h : e.1 with
      | integer i => exact ⟨i.toNat + 1, fun m hm e' => by simp only [Term.integer.injEq] at e'; omega⟩
      | _ => exact ⟨0, fun m _ e' => by cases e'⟩
    refine ⟨max n j, fun m hm => ?_⟩
    have ne : ¬compareExact (fuel (.integer (m : Int)) e.1) (.integer (m : Int)) e.1 = .eq := by
      rw [integer_compareExact_eq]; exact hj m (by omega)
    simpa [mapLookup, List.find?_cons, ne] using hn m (by omega)

theorem posOk_of {E' : Term → Prop} {n : Nat} {P : List (Term × List Term × Term)}
    (h : ∀ p ∈ P, FunLit E' n (.tuple #[p.1, Term.list p.2.1, p.2.2])) : PosOk E' n P := by
  intro p mp
  obtain ⟨k, args, ret, e, len, ha, hr⟩ := h p mp
  obtain ⟨-, el, er⟩ := enc_inj e
  rw [el, er]
  exact ⟨ha, hr, by omega⟩

theorem not_seen_any {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {h x : Term} (hx : lh x < N) :
    S.any (fun e => Term.compareExact (Term.fuel (.cons h x) e.1) (.cons h x) e.1 == .eq) = Bool.false := by
  simp only [List.any_eq_false, beq_iff_eq]
  intro e me hit
  obtain ⟨h', b, e₁, one, hb⟩ := hS e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
  omega

/-- Function types of element types decide whether they hold functions, under seen sets above them, given
complete subtyping of element types. -/
theorem funA_empty (ef : EF nd E V den tl K)
    (subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true"))
    {x : Term} (fx : FunA E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 11 ≤ m → Elixir.Module.Types.Descr.«fun_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ (n : Nat) (g : List (FunSem.Row V)),
        (∀ r ∈ g, FunSem.ValidRow n r) → arityOf x (.integer n) (valF E den g) = Bool.false) := by
  have fx' := fx
  obtain ⟨p, R, rfl, ne, bR, kR⟩ := fx'
  -- Totality, for any seen set.
  generalize hH0 : lh (.tuple #[.atom (if p then "union" else "negation"), .map R]) + 1 = H0
  have hnone : EB E H0 (.map []) := ⟨ef.none, by rw [lh_nil_map]; omega⟩
  have ff : FField (EB E H0) (.tuple #[.atom (if p then "union" else "negation"), .map R]) := by
    refine ⟨p, R, rfl, fun q v h => ?_⟩
    obtain ⟨n, hn⟩ := kR q (by rw [h]; rfl)
    have le : lh v ≤ lh (.tuple #[.atom (if p then "union" else "negation"), .map R]) := by
      rw [lh_tag]; exact lookup_lh h
    refine (litB_of (bR q v h) hn).mono fun t ht => ⟨n, hn, funLit_mono (fun a ha => ⟨ha.1, ?_⟩) ht⟩
    have := ha.2; omega
  obtain ⟨b₀, run₀⟩ := fun_total ((ef.ops H0 (by omega)).mono (by omega : K ≤ K + 3)) ((ef.dops H0).mono (by omega))
    ((ef.funB H0).mono (by omega)) (domOk (ef.ops H0 (by omega)) (ef.dops H0) (ef.funB H0) hnone (ef.tailB H0)) hnone ff S
  refine ⟨b₀, fun m hm => run₀ m (by omega), fun N hx hS => ?_⟩
  cases p
  · have : b₀ = Bool.false := by
      have := run₀ (K + 8) (Nat.le_refl _)
      unfold Elixir.Module.Types.Descr.«fun_empty?/2» at this
      cases b₀ <;> simp_all [boolAtom]
    subst this
    obtain ⟨n₀, hn₀⟩ := fresh_arities R
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    have := h n₀ [] (by simp)
    simp [arityOf, hn₀ n₀ (Nat.le_refl _)] at this
  · have hl : ∀ b n t, LitB E b n t → FunLit E n t := fun _ _ _ h => funLit_mono (fun a ha => ha.1) h
    have hR : ∀ e ∈ mapEntries R, ∃ n : Nat, e.1 = .integer n ∧ Bdd (LitB E e.2 n) e.2 := by
      intro e me
      have h := mapLookup_of_mem_mapEntries me
      obtain ⟨n, hn⟩ := kR e.1 (by rw [h]; rfl)
      exact ⟨n, hn, litB_of (bR _ _ h) hn⟩
    have below : ∀ e ∈ mapEntries R, lh e.2 < N := by
      intro e me
      have := le_lh_map me
      rw [lh_tag] at hx
      omega
    obtain ⟨b₁, run₁, sem₁⟩ := fun_union_sem (K := K + 9) ef.congrE R S (LitB E) hl hR
      (fun e me => not_seen_any hS (below e me)) (by
        intro e me n hn P N' hP hN LP LN
        have one : 1 ≤ lh e.2 := fbdd_pos (bR _ _ (mapLookup_of_mem_mapEntries me)) fun _ ht => funArity_shape ht
        have hS' : SafeN (lh e.2) ((.cons e.1 e.2, .atom "true") :: S) := by
          intro s ms
          rcases List.mem_cons.mp ms with rfl | ms
          · exact ⟨e.1, e.2, rfl, one, Nat.le_refl _⟩
          · obtain ⟨h', b', e₁, one', hb'⟩ := hS s ms
            exact ⟨h', b', e₁, one', by have := below e me; omega⟩
        have hT : SafeT (lh e.2 + 1) ((.cons e.1 e.2, .atom "true") :: S) := by
          intro s ms
          rcases List.mem_cons.mp ms with rfl | ms
          · exact ⟨e.1, e.2, rfl, one, Or.inr ⟨⟨n, hn⟩, Nat.le_refl _⟩⟩
          · obtain ⟨h', b', e₁, one', hb'⟩ := hS s ms
            exact ⟨h', b', e₁, one', Or.inl (by have := below e me; omega)⟩
        exact fun_line_sem ((felem ef subc one hS').mono (by omega : K ≤ K + 6)) (fdom ef one hT) n P N'
          (posOk_of LP) (posOk_of LN))
    have : b₀ = b₁ := by
      have := (run₀ (K + 11) (by omega)).symm.trans (run₁ (K + 11) (by omega))
      cases b₀ <;> cases b₁ <;> simp_all [boolAtom]
    subst this
    rw [sem₁]
    exact forall_congr' fun n => forall_congr' fun g => imp_congr_right fun _ => by rw [arity_tag]; simp

/-- Function types of element types, whose points are functions: closed under plain operations, which keep literal
heights, with exact emptiness under seen sets above them, given complete subtyping of element types. -/
theorem funAC (ef : EF nd E V den tl K)
    (subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true")) :
    FunC (K + 11) (FunA E) (FVal E den) (fun _ => True) True where
  funF := FunA.funF
  union := fun {x y} hx hy m w hm run => by
    obtain ⟨w', run', fw, le⟩ := funA_union hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run'] at run; cases run
    exact ⟨fw, fun _ => le⟩
  inter := fun {x y} hx hy m w hm run kw => by
    obtain ⟨w', run', k⟩ := funA_inter hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run'] at run; cases run
    exact ⟨(k kw).1, fun _ => (k kw).2⟩
  diff := fun {x y} hx hy m w hm run kw => by
    obtain ⟨w', run', k⟩ := funA_diff hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run'] at run; cases run
    exact ⟨(k kw).1, fun _ => (k kw).2⟩
  empty := fun {x} S {m} hx _ hm => by
    obtain ⟨b, run, ex⟩ := funA_empty ef subc hx S
    have key : Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "fun") x (.map S) = .ok (boolAtom b) := by
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m hm
    refine ⟨fun N hN hS none => ?_, fun _ => ⟨b, key, fun N hN hS hb p r f => ?_⟩⟩
    · have : b = Bool.true := (ex N hN hS).mpr fun n g vg => by
        have := none (0, .integer n, valF E den g) (valF_resp g) ⟨n, g, rfl, vg, rfl⟩
        rwa [dn_fun] at this
      rw [key, this]; rfl
    · obtain ⟨n, g, ha, vg, hρ⟩ := f
      rw [dn_fun, ha, hρ]
      exact (ex N hN hS).mp hb n g vg

end

end Elixir.STTDescrProofsTest.Nest
