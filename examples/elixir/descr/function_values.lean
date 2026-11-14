/-! Function values of arity n are finite graphs of rows (x, y): each argument x_j is a value or the probe ★
(`none`), and the result y is a value or the error Ω (`none`). The row (★ⁿ, Ω) is not allowed, so the top
function of arity n is the arrow (none, …, none) → term. A function belongs to an arrow when every row whose
arguments are ★ or in the arrow's arguments returns a value in the arrow's return. -/

namespace Elixir.STTDescrProofsTest.FunSem

variable {V : Type}

abbrev Row (V : Type) := List (Option V) × Option V
abbrev Arrow (V : Type) := List (V → Prop) × (V → Prop)

/-- An argument or a result: a value of the set, or, when not flagged, ★ or Ω. -/
def Opt (flag : Bool) (a : V → Prop) : Option V → Prop
  | none => flag = false
  | some v => a v

/-- The arguments a row passes to an arrow: ★ or members of the arrow's argument types. -/
def InDom : List (V → Prop) → List (Option V) → Prop
  | [], [] => True
  | t :: ts, o :: os => Opt false t o ∧ InDom ts os
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- A row an arrow allows: when the arrow applies, the row returns a value of its return type. -/
def Allows (a : Arrow V) (r : Row V) : Prop :=
  InDom a.1 r.1 → ∃ y, r.2 = some y ∧ a.2 y

/-- The flagged arguments of `phi`: each one is a value of its set, or ★ when not flagged. -/
def Args : List (Bool × (V → Prop)) → List (Option V) → Prop
  | [], [] => True
  | (b, a) :: as, o :: os => Opt b a o ∧ Args as os
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- No row with these arguments and result is allowed by all the arrows. -/
def NoRow (args : List (Bool × (V → Prop))) (ret : Bool × (V → Prop)) (P : List (Arrow V)) : Prop :=
  ∀ x y, Args args x → Opt ret.1 ret.2 y → ¬∀ p ∈ P, Allows p (x, y)

/-- The arguments of the recursive calls that skip an arrow through each of its arguments. -/
def Skips : List (V → Prop) → List (Bool × (V → Prop)) → List (List (Bool × (V → Prop)))
  | u :: us, (b, a) :: as => ((true, fun v => a v ∧ ¬u v) :: as) :: (Skips us as).map ((b, a) :: ·)
  | [], _ => []
  | _ :: _, [] => []

/-- The `phi` recursion over sets, without its shortcuts. -/
def phiS (args : List (Bool × (V → Prop))) (ret : Bool × (V → Prop)) : List (Arrow V) → Prop
  | [] => (∃ p ∈ args, p.1 = true ∧ ∀ v, ¬p.2 v) ∨ (ret.1 = true ∧ ∀ v, ¬ret.2 v)
  | (us, s) :: P => phiS args (true, fun v => ret.2 v ∧ s v) P ∧ ∀ a ∈ Skips us args, phiS a ret P

theorem opt_exists (b : Bool) (a : V → Prop) : (∃ o, Opt b a o) ↔ (b = true → ∃ v, a v) := by
  constructor
  · rintro ⟨o, h⟩ hb
    cases o with
    | none => simp [Opt] at h; simp_all
    | some v => exact ⟨v, h⟩
  · intro h
    cases b
    · exact ⟨none, rfl⟩
    · obtain ⟨v, hv⟩ := h rfl; exact ⟨some v, hv⟩

theorem args_exists : ∀ (args : List (Bool × (V → Prop))),
    (∃ x, Args args x) ↔ ∀ p ∈ args, p.1 = true → ∃ v, p.2 v
  | [] => ⟨fun _ => by simp, fun _ => ⟨[], trivial⟩⟩
  | (b, a) :: as => by
    constructor
    · rintro ⟨x, h⟩
      cases x with
      | nil => cases h
      | cons o os =>
        obtain ⟨ho, hs⟩ := h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (opt_exists b a).mp ⟨o, ho⟩
        · exact (args_exists as).mp ⟨os, hs⟩ p hp
    · intro h
      obtain ⟨o, ho⟩ := (opt_exists b a).mpr (h (b, a) (by simp))
      obtain ⟨os, hs⟩ := (args_exists as).mpr fun p hp => h p (by simp [hp])
      exact ⟨o :: os, ho, hs⟩

/-- Arguments outside an arrow's domain are those of a call that skips the arrow through one argument. -/
theorem args_skips : ∀ (us : List (V → Prop)) (args : List (Bool × (V → Prop))) (x : List (Option V)),
    us.length = args.length → ((Args args x ∧ ¬InDom us x) ↔ ∃ a ∈ Skips us args, Args a x)
  | [], [], x, _ => by
    cases x <;> simp [Args, InDom, Skips]
  | u :: us, (b, a) :: as, x, len => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at len
    cases x with
    | nil => simp [Args, Skips]
    | cons o os =>
      have ih := args_skips us as os len
      simp only [Args, InDom, Skips, List.mem_cons, List.mem_map]
      constructor
      · rintro ⟨⟨ho, hs⟩, hn⟩
        by_cases hu : Opt false u o
        · have : ¬InDom us os := fun h => hn ⟨hu, h⟩
          obtain ⟨a', ma, ha⟩ := ih.mp ⟨hs, this⟩
          exact ⟨_, Or.inr ⟨a', ma, rfl⟩, ho, ha⟩
        · cases o with
          | none => exact absurd rfl hu
          | some v => exact ⟨_, Or.inl rfl, ⟨ho, hu⟩, hs⟩
      · rintro ⟨a', ha' | ⟨a'', ma, rfl⟩, hx⟩
        · subst ha'
          obtain ⟨ho, hs⟩ := hx
          cases o with
          | none => cases ho
          | some v => exact ⟨⟨ho.1, hs⟩, fun h => ho.2 h.1⟩
        · obtain ⟨ho, hs⟩ := hx
          obtain ⟨hs', hn⟩ := ih.mpr ⟨a'', ma, hs⟩
          exact ⟨⟨ho, hs'⟩, fun h => hn h.2⟩
  | [], _ :: _, _, len => by simp at len
  | _ :: _, [], _, len => by simp at len

theorem skips_length : ∀ (us : List (V → Prop)) (args : List (Bool × (V → Prop))), ∀ a ∈ Skips us args,
    a.length = args.length
  | u :: us, (b, a) :: as, a', ma => by
    simp only [Skips, List.mem_cons, List.mem_map] at ma
    rcases ma with rfl | ⟨a'', ma, rfl⟩
    · rfl
    · simp [skips_length us as a'' ma]
  | [], _, _, ma => by simp [Skips] at ma
  | _ :: _, [], _, ma => by simp [Skips] at ma

/-- `phi` holds exactly when no row with its arguments and result is allowed by all the arrows. -/
theorem phiS_iff (args : List (Bool × (V → Prop))) (ret : Bool × (V → Prop)) (P : List (Arrow V))
    (len : ∀ p ∈ P, p.1.length = args.length) : phiS args ret P ↔ NoRow args ret P := by
  induction P generalizing args ret with
  | nil =>
    simp only [phiS, NoRow, List.not_mem_nil, false_implies, implies_true, not_true_eq_false, imp_false]
    constructor
    · rintro (⟨p, mp, hb, he⟩ | ⟨hb, he⟩) x y hx hy
      · obtain ⟨v, hv⟩ := (args_exists args).mp ⟨x, hx⟩ p mp hb
        exact he v hv
      · obtain ⟨v, hv⟩ := (opt_exists ret.1 ret.2).mp ⟨y, hy⟩ hb
        exact he v hv
    · intro h
      apply Classical.byContradiction
      intro hn
      simp only [not_or, not_exists, not_and, Classical.not_forall, Classical.not_not] at hn
      obtain ⟨x, hx⟩ := (args_exists args).mpr fun p mp hb => by
        obtain ⟨v, hv⟩ := hn.1 p mp hb; exact ⟨v, hv⟩
      obtain ⟨y, hy⟩ := (opt_exists ret.1 ret.2).mpr fun hb => by
        obtain ⟨v, hv⟩ := hn.2 hb; exact ⟨v, hv⟩
      exact h x y hx hy
  | cons p P ih =>
    obtain ⟨us, s⟩ := p
    have lu : us.length = args.length := len (us, s) (by simp)
    have lP : ∀ p ∈ P, p.1.length = args.length := fun p mp => len p (by simp [mp])
    simp only [phiS]
    rw [ih args _ lP]
    have skips : (∀ a ∈ Skips us args, phiS a ret P) ↔ ∀ a ∈ Skips us args, NoRow a ret P := by
      refine forall₂_congr fun a ma => ih a ret fun p mp => ?_
      rw [skips_length us args a ma]; exact lP p mp
    rw [skips]
    constructor
    · rintro ⟨hu, hs⟩ x y hx hy hall
      by_cases hd : InDom us x
      · obtain ⟨v, rfl, hv⟩ := hall (us, s) (by simp) hd
        exact hu x (some v) hx ⟨hy, hv⟩ fun p mp => hall p (by simp [mp])
      · obtain ⟨a, ma, ha⟩ := (args_skips us args x lu).mp ⟨hx, hd⟩
        exact hs a ma x y ha hy fun p mp => hall p (by simp [mp])
    · intro h
      refine ⟨fun x y hx hy hall => ?_, fun a ma x y ha hy hall => ?_⟩
      · cases y with
        | none => cases hy
        | some v =>
          refine h x (some v) hx hy.1 fun p mp => ?_
          rcases List.mem_cons.mp mp with rfl | mp
          · exact fun _ => ⟨v, rfl, hy.2⟩
          · exact hall p mp
      · have hx := (args_skips us args x lu).mpr ⟨a, ma, ha⟩
        refine h x y hx.1 hy fun p mp => ?_
        rcases List.mem_cons.mp mp with rfl | mp
        · exact fun hd => absurd hd hx.2
        · exact hall p mp

/-! Functions and lines of arrows. -/

/-- Rows of a function of arity n: n arguments, and never the probe input with the error. -/
def ValidRow (n : Nat) (r : Row V) : Prop :=
  r.1.length = n ∧ ¬(r.1 = List.replicate n none ∧ r.2 = none)

/-- A line of arrows is empty when every function of arity n in its positive arrows is in one of its negative ones. -/
def LineEmpty (n : Nat) (P N : List (Arrow V)) : Prop :=
  ∀ g : List (Row V), (∀ r ∈ g, ValidRow n r) → (∀ p ∈ P, ∀ r ∈ g, Allows p r) → ∃ q ∈ N, ∀ r ∈ g, Allows q r

/-- The rows the positive arrows allow, one per negative arrow, that this negative arrow does not allow. -/
theorem witness_rows (n : Nat) (P : List (Arrow V)) : ∀ N : List (Arrow V),
    (∀ q ∈ N, ∃ r, ValidRow n r ∧ (∀ p ∈ P, Allows p r) ∧ ¬Allows q r) →
    ∃ g : List (Row V), (∀ r ∈ g, ValidRow n r ∧ ∀ p ∈ P, Allows p r) ∧ ∀ q ∈ N, ∃ r ∈ g, ¬Allows q r
  | [], _ => ⟨[], by simp, by simp⟩
  | q :: N, h => by
    obtain ⟨r, vr, ar, nr⟩ := h q (by simp)
    obtain ⟨g, hg, ng⟩ := witness_rows n P N fun q' mq => h q' (by simp [mq])
    refine ⟨r :: g, fun r' mr => ?_, fun q' mq => ?_⟩
    · rcases List.mem_cons.mp mr with rfl | mr
      · exact ⟨vr, ar⟩
      · exact hg r' mr
    · rcases List.mem_cons.mp mq with rfl | mq
      · exact ⟨r, by simp, nr⟩
      · obtain ⟨r', mr, nr'⟩ := ng q' mq; exact ⟨r', by simp [mr], nr'⟩

/-- A line is empty exactly when one negative arrow contains the positive arrows on every row. -/
theorem lineEmpty_iff (n : Nat) (P N : List (Arrow V)) :
    LineEmpty n P N ↔ ∃ q ∈ N, ∀ r, ValidRow n r → (∀ p ∈ P, Allows p r) → Allows q r := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    simp only [not_exists, not_and, Classical.not_forall] at hn
    obtain ⟨g, hg, ng⟩ := witness_rows n P N fun q mq => by
      obtain ⟨r, hr⟩ := hn q mq
      exact ⟨r, hr.1, hr.2.1, hr.2.2⟩
    obtain ⟨q, mq, hq⟩ := h g (fun r mr => (hg r mr).1) (fun p mp r mr => (hg r mr).2 p mp)
    obtain ⟨r, mr, nr⟩ := ng q mq
    exact nr (hq r mr)
  · rintro ⟨q, mq, hq⟩ g vg pg
    exact ⟨q, mq, fun r mr => hq r (vg r mr) fun p mp => pg p mp r mr⟩

theorem inDom_args : ∀ (ts : List (V → Prop)) (x : List (Option V)), InDom ts x ↔ Args (ts.map (false, ·)) x
  | [], [] => Iff.rfl
  | t :: ts, o :: os => by simp only [InDom, List.map, Args, inDom_args ts os]
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl

theorem inDom_probe : ∀ (ts : List (V → Prop)), InDom ts (List.replicate ts.length none)
  | [] => trivial
  | _ :: ts => ⟨rfl, inDom_probe ts⟩

theorem inDom_length : ∀ {ts : List (V → Prop)} {x : List (Option V)}, InDom ts x → x.length = ts.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [inDom_length h.2]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- With some positive arrow of arity n, a negative arrow contains them on every row exactly when `phi` holds,
starting from its arguments and the complement of its return. -/
theorem neg_iff_phi (n : Nat) (P : List (Arrow V)) (ne : P ≠ []) (lP : ∀ p ∈ P, p.1.length = n)
    (t : List (V → Prop)) (s : V → Prop) (lt : t.length = n) :
    (∀ r, ValidRow n r → (∀ p ∈ P, Allows p r) → Allows (t, s) r) ↔
      phiS (t.map (false, ·)) (false, fun v => ¬s v) P := by
  rw [phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [lt])]
  constructor
  · intro h x y hx hy hall
    have hd : InDom t x := (inDom_args t x).mpr hx
    have lx : x.length = n := by rw [inDom_length hd, lt]
    have valid : ValidRow n (x, y) := by
      refine ⟨lx, fun ⟨ex, ey⟩ => ?_⟩
      dsimp only at ex ey
      obtain ⟨p, mp⟩ := List.exists_mem_of_ne_nil P ne
      have : InDom p.1 x := by rw [ex, ← lP p mp]; exact inDom_probe p.1
      obtain ⟨v, hv, -⟩ := hall p mp this
      rw [ey] at hv; cases hv
    obtain ⟨v, rfl, hv⟩ := h (x, y) valid hall hd
    exact hy hv
  · intro h r vr hall hd
    apply Classical.byContradiction
    intro hn
    refine h r.1 r.2 ((inDom_args t r.1).mp hd) ?_ hall
    cases hr : r.2 with
    | none => rfl
    | some v => exact fun hv => hn ⟨v, hr, hv⟩

/-- The top arrow of arity n allows every row of a function of arity n. -/
def top (n : Nat) : Arrow V := (List.replicate n (fun _ => False), fun _ => True)

theorem inDom_none : ∀ (n : Nat) (x : List (Option V)), InDom (List.replicate n (fun _ : V => False)) x →
    x = List.replicate n none
  | 0, [], _ => rfl
  | n + 1, o :: os, h => by
    obtain ⟨ho, hs⟩ := h
    cases o with
    | none => simp [inDom_none n os hs, List.replicate_succ]
    | some v => exact ho.elim
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h

theorem allows_top {n : Nat} {r : Row V} (vr : ValidRow n r) : Allows (top n) r := by
  intro hd
  have ex := inDom_none n r.1 hd
  cases hr : r.2 with
  | none => exact absurd ⟨ex, hr⟩ vr.2
  | some v => exact ⟨v, rfl, trivial⟩

/-- Lines without positive arrows are the lines with the top arrow as their only positive one. -/
theorem lineEmpty_top (n : Nat) (N : List (Arrow V)) : LineEmpty n [] N ↔ LineEmpty n [top n] N := by
  rw [lineEmpty_iff, lineEmpty_iff]
  refine exists_congr fun q => and_congr_right fun _ => forall_congr' fun r => ?_
  constructor
  · intro h vr _; exact h vr (by simp)
  · intro h vr _; exact h vr fun p mp => by simp at mp; subst mp; exact allows_top vr

theorem lineEmpty_nil (n : Nat) : ¬LineEmpty n ([] : List (Arrow V)) [] := by
  intro h
  obtain ⟨q, mq, -⟩ := h [] (by simp) (by simp)
  cases mq

end Elixir.STTDescrProofsTest.FunSem
