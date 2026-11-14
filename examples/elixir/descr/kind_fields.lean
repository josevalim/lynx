namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fields of types, over the structural kinds. -/

/-- Fields: non-empty bitmaps and atom types, function fields `Fn`, and the fields of the structural kinds. -/
def FieldC (Fn TF LF MF : Term → Prop) (name : String) (x : Term) : Prop :=
  (name = "bitmap" ∧ BitField x) ∨ (name = "atom" ∧ AtomF x) ∨ (name = "fun" ∧ Fn x) ∨
    (name = "list" ∧ LF x) ∨ (name = "tuple" ∧ TF x) ∨ (name = "map" ∧ MF x)

/-- Points of fields: bitmaps hold bit indices, the structural kinds hold valuations from values, and function
types hold an arity and a valuation `FV` allows. -/
def PtOkC (TV LV MV : (Term → Bool) → Prop) (FV : Term → (Term → Bool) → Prop) (name : String) (p : Point) : Prop :=
  Resp p.2.2 ∧ (name = "bitmap" → p.1 < 8) ∧ (name = "list" → LV p.2.2) ∧ (name = "tuple" → TV p.2.2) ∧
    (name = "map" → MV p.2.2) ∧ (name = "fun" → FV p.2.1 p.2.2)

/-- Function points with any arity and valuation. -/
abbrev FVT : Term → (Term → Bool) → Prop := fun _ _ => True

/-- The three structural kinds. -/
structure Kinds (K : Nat) (TF LF MF : Term → Prop) (TV LV MV : (Term → Bool) → Prop) : Prop where
  t : KindOk K "tuple" TF TV
  l : KindOk K "list" LF LV
  m : KindOk K "map" MF MV

/-- Function fields `Fn`, whose points `FV` allows: function types, closed under plain operations, whose emptiness
is complete on the seen sets `FS` below them, at call depths from `K`. When `H` holds, the plain operations keep
literal heights, and emptiness is decided and sound. -/
structure FunC (K : Nat) (Fn : Term → Prop) (FV : Term → (Term → Bool) → Prop) (FS : List (Term × Term) → Prop)
    (H : Prop) : Prop where
  funF : ∀ {x}, Fn x → FunF x
  union : ∀ {x y}, Fn x → Fn y → ∀ m w, K ≤ m →
    Elixir.Module.Types.Descr.«bare_union/3» (D m) (.atom "fun") x y = .ok w → Fn w ∧ (H → lh w ≤ max (lh x) (lh y))
  inter : ∀ {x y}, Fn x → Fn y → ∀ m w, K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom "fun") x y = .ok w →
    kept (.atom "fun", w) = Bool.true → Fn w ∧ (H → lh w ≤ max (lh x) (lh y))
  diff : ∀ {x y}, Fn x → Fn y → ∀ m w, K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom "fun") x y = .ok w →
    kept (.atom "fun", w) = Bool.true → Fn w ∧ (H → lh w ≤ max (lh x) (lh y))
  empty : ∀ {x} (S : List (Term × Term)) {m}, Fn x → FS S → K ≤ m →
    (∀ N, lh x < N → SafeN N S → (∀ p : Point, Resp p.2.2 → FV p.2.1 p.2.2 → dn "fun" (some x) p = Bool.false) →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "fun") x (.map S) = .ok (.atom "true")) ∧
    (H → ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "fun") x (.map S) = .ok (boolAtom b) ∧
      ∀ N, lh x < N → SafeN N S → b = Bool.true →
        ∀ p : Point, Resp p.2.2 → FV p.2.1 p.2.2 → dn "fun" (some x) p = Bool.false)

theorem lh_int (n : Int) : lh (.integer n) = 0 := by simp [lh]

theorem lh_set {S : List (Term × Term)} (set : Erlang.sets.elements? (.map S) = some S) : lh (.map S) = 0 := by
  refine Nat.le_zero.mp (lh_map_le.mpr fun e' me' => ?_)
  simp only [Erlang.sets.elements?] at set
  split at set
  · rename_i all
    have := List.all_eq_true.mp all e' me'
    match e', this with
    | (_, .nil), _ => simp [lh]
  · cases set

theorem lh_atomF {x : Term} (h : AtomF x) : lh x = 0 := by
  obtain ⟨⟨p, S, rfl, set⟩, -⟩ := h
  show lh (.tuple ⟨[_, _]⟩) = 0
  cases p <;> simp [lh, lh_set set]

theorem lh_bitF {x : Term} (h : BitField x) : lh x = 0 := by
  obtain ⟨b, rfl, -⟩ := h
  exact lh_int _

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

theorem fieldC_cases {name : String} {x : Term} (h : FieldC Fn TF LF MF name x) :
    name = "bitmap" ∨ name = "atom" ∨ name = "fun" ∨ name = "list" ∨ name = "tuple" ∨ name = "map" := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem fieldC_bitmap {x : Term} (h : FieldC Fn TF LF MF "bitmap" x) : BitField x := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_atom {x : Term} (h : FieldC Fn TF LF MF "atom" x) : AtomF x := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_fun {x : Term} (h : FieldC Fn TF LF MF "fun" x) : Fn x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_list {x : Term} (h : FieldC Fn TF LF MF "list" x) : LF x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_tuple {x : Term} (h : FieldC Fn TF LF MF "tuple" x) : TF x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_map {x : Term} (h : FieldC Fn TF LF MF "map" x) : MF x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> first | exact h | simp at h

/-- Plain unions of fields. -/
theorem fieldC_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m) {name : String}
    {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_union/3» (D m) (.atom name) x y = .ok w ∧ FieldC Fn TF LF MF name w ∧
      (∀ p, PtOkC TV LV MV FV name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
      (H → lh w ≤ max (lh x) (lh y)) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, fw, sem⟩ := bit_union (D m) (fieldC_bitmap fx) (fieldC_bitmap fy)
    exact ⟨w, run, Or.inl ⟨rfl, fw⟩, fun p _ => by simp [dn_bitmap, sem], fun _ => by rw [lh_bitF fw]; omega⟩
  · obtain ⟨w, run, fw, sem⟩ := atom_union_spec (D m) (fieldC_atom fx) (fieldC_atom fy)
    exact ⟨w, run, Or.inr (Or.inl ⟨rfl, fw⟩), fun p _ => by simp [dn_atom, sem], fun _ => by rw [lh_atomF fw]; omega⟩
  · obtain ⟨n, rfl, -⟩ := succ_of_le hm
    obtain ⟨w, run, -, sem⟩ := fun_union_spec n (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fy))
    obtain ⟨fw, le⟩ := fc.union (fieldC_fun fx) (fieldC_fun fy) _ w (by omega) run
    exact ⟨w, run, Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), fun p ok => by simp [dn_fun, sem _ _ ok.1], le⟩
  · obtain ⟨w, run, fw, sem, le⟩ := ks.l.union (fieldC_list fx) (fieldC_list fy)
    exact ⟨w, run m (by omega), Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))), fun p ok => sem p (ok.2.2.1 rfl), fun _ => le⟩
  · obtain ⟨w, run, fw, sem, le⟩ := ks.t.union (fieldC_tuple fx) (fieldC_tuple fy)
    exact ⟨w, run m (by omega), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))),
      fun p ok => sem p (ok.2.2.2.1 rfl), fun _ => le⟩
  · obtain ⟨w, run, fw, sem, le⟩ := ks.m.union (fieldC_map fx) (fieldC_map fy)
    exact ⟨w, run m (by omega), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw⟩)))),
      fun p ok => sem p (ok.2.2.2.2.1 rfl), fun _ => le⟩

theorem kept_of_ne {name : String} {w : Term} (k : kept (.atom name, w) = Bool.false) :
    w = .integer 0 ∨ w = .atom "bdd_bot" := by
  simp only [kept, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at k
  rcases k with k | k
  · exact Or.inl ((compareExact_eq_integer _ _).mp k)
  · exact Or.inr ((compareExact_eq_atom _ _).mp k)

/-- Plain intersections of fields. -/
theorem fieldC_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m) {name : String}
    {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (H → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, k, d⟩ := bit_inter (D m) (fieldC_bitmap fx) (fieldC_bitmap fy)
    refine ⟨w, run, fun kw => ⟨Or.inl ⟨rfl, (k kw).1⟩, fun _ => by rw [lh_bitF (k kw).1]; omega⟩, fun p _ => ?_⟩
    cases kw : kept (.atom "bitmap", w)
    · simp [keptO_false kw, dn_none, dn_bitmap, d kw]
    · simp [keptO_true kw, dn_bitmap, (k kw).2]
  · obtain ⟨w, run, k, d⟩ := atom_inter_spec (D m) (fieldC_atom fx) (fieldC_atom fy)
    refine ⟨w, run, fun kw => ⟨Or.inr (Or.inl ⟨rfl, (k kw).1⟩), fun _ => by rw [lh_atomF (k kw).1]; omega⟩, fun p _ => ?_⟩
    cases kw : kept (.atom "atom", w)
    · simp [keptO_false kw, dn_none, dn_atom, d kw]
    · simp [keptO_true kw, dn_atom, (k kw).2]
  · obtain ⟨n, rfl, -⟩ := succ_of_le hm
    obtain ⟨w, run, k, d⟩ := fun_inter_spec n (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fy))
    refine ⟨w, run, fun kw => ?_, fun p ok => ?_⟩
    · obtain ⟨fw, le⟩ := fc.inter (fieldC_fun fx) (fieldC_fun fy) _ w (by omega) run kw
      exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), le⟩
    cases kw : kept (.atom "fun", w)
    · simp [keptO_false kw, dn_none, dn_fun, d kw _ _ ok.1]
    · simp [keptO_true kw, dn_fun, (k kw).2 _ _ ok.1]
  · obtain ⟨w, run, k, sem⟩ := ks.l.inter (fieldC_list fx) (fieldC_list fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.t.inter (fieldC_tuple fx) (fieldC_tuple fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.m.inter (fieldC_map fx) (fieldC_map fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Plain differences of fields. -/
theorem fieldC_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m) {name : String}
    {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (H → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, rfl, a₁, a₂⟩ := fieldC_bitmap fx
    obtain ⟨b, rfl, b₁, b₂⟩ := fieldC_bitmap fy
    obtain ⟨r, run, ok, bm, -⟩ := diff_key "bitmap" _ _ (Or.inl ⟨rfl, a, rfl, a₁, a₂⟩) (Or.inl ⟨rfl, b, rfl, b₁, b₂⟩)
    obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
    have ea' : a = a' := by simp only [Term.integer.injEq] at ea; exact_mod_cast ea
    have eb' : b = b' := by simp only [Term.integer.injEq] at eb; exact_mod_cast eb
    subst ea' eb'
    refine ⟨_, run _, fun kw => ⟨?_, fun _ => by rw [lh_int]; omega⟩, fun p _ => ?_⟩
    · rcases ok kw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
      · exact Or.inl ⟨rfl, h⟩
      · simp at h
      · exact absurd rfl h
    · cases kw : kept (.atom "bitmap", Term.integer ↑(a - (a &&& b)))
      · simp [kept] at kw
        have : (a - (a &&& b)).testBit p.1 = Bool.false := by
          have z : a - (a &&& b) = 0 := by omega
          rw [z]; simp
        rw [testBit_sub_and] at this
        simpa [keptO_false (show kept (.atom "bitmap", Term.integer ↑(a - (a &&& b))) = Bool.false by simp [kept]; omega),
          dn_none, dn_bitmap, bitOf_nat] using this.symm
      · simp [keptO_true kw, dn_bitmap, bitOf_nat, testBit_sub_and]
  · obtain ⟨r, run, ok, -, am, -⟩ := diff_key "atom" x y (Or.inr (Or.inl ⟨rfl, fieldC_atom fx⟩))
      (Or.inr (Or.inl ⟨rfl, fieldC_atom fy⟩))
    refine ⟨r, run _, fun kw => ?_, fun p _ => ?_⟩
    · rcases ok kw with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩
      · simp at h
      · exact ⟨Or.inr (Or.inl ⟨rfl, h⟩), fun _ => by rw [lh_atomF h]; omega⟩
      · exact absurd rfl h
    · have := am rfl p.2.1
      cases kw : kept (.atom "atom", r)
      · rw [kw] at this
        simp only [Bool.false_eq_true, ite_false] at this
        have h0 : amemV Option.none p.2.1 = Bool.false := rfl
        rw [h0] at this
        simp [keptO_false kw, dn_none, dn_atom, ← this]
      · rw [kw] at this
        simpa [keptO_true kw, dn_atom] using this
  · obtain ⟨n, rfl, -⟩ := succ_of_le (show 1 + 1 ≤ m by omega)
    obtain ⟨w, run, k, d⟩ := fun_diff_spec n (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fy))
    refine ⟨w, run, fun kw => ?_, fun p ok => ?_⟩
    · obtain ⟨fw, le⟩ := fc.diff (fieldC_fun fx) (fieldC_fun fy) _ w (by omega) run kw
      exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), le⟩
    cases kw : kept (.atom "fun", w)
    · simp [keptO_false kw, dn_none, dn_fun, d kw _ _ ok.1]
    · simp [keptO_true kw, dn_fun, (k kw).2 _ _ ok.1]
  · obtain ⟨w, run, k, sem⟩ := ks.l.diff (fieldC_list fx) (fieldC_list fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.t.diff (fieldC_tuple fx) (fieldC_tuple fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.m.diff (fieldC_map fx) (fieldC_map fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Optimized unions of fields. -/
theorem fieldC_opt_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {name : String} {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_union/4» (D m) (.atom name) x y (.map S) = .ok w ∧ FieldC Fn TF LF MF name w ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, fw, sem, -⟩ := fieldC_union ks fc hm fx fy
    exact ⟨w, by rw [opt_union4_eq _ (Or.inl rfl)]; exact run, fw, sem⟩
  · obtain ⟨w, run, fw, sem, -⟩ := fieldC_union ks fc hm fx fy
    exact ⟨w, by rw [opt_union4_eq _ (Or.inr (Or.inl rfl))]; exact run, fw, sem⟩
  · obtain ⟨w, run, fw, sem, -⟩ := fieldC_union ks fc hm fx fy
    exact ⟨w, by rw [opt_union4_eq _ (Or.inr (Or.inr (Or.inl rfl)))]; exact run, fw, sem⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.l.opt_union S (fieldC_list fx) (fieldC_list fy) (show K ≤ m by omega)
    exact ⟨w, run, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))), fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.t.opt_union S (fieldC_tuple fx) (fieldC_tuple fy) (show K ≤ m by omega)
    exact ⟨w, run, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))), fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.m.opt_union S (fieldC_map fx) (fieldC_map fy) (show K ≤ m by omega)
    exact ⟨w, run, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw⟩)))), fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Optimized intersections of fields. -/
theorem fieldC_opt_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {name : String} {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom name) x y (.map S) = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy
    exact ⟨w, by rw [opt_inter4_eq _ (Or.inl rfl)]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy
    exact ⟨w, by rw [opt_inter4_eq _ (Or.inr (Or.inl rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy
    exact ⟨w, by rw [opt_inter4_eq _ (Or.inr (Or.inr rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.l.opt_inter S (fieldC_list fx) (fieldC_list fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩))), fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.t.opt_inter S (fieldC_tuple fx) (fieldC_tuple fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.m.opt_inter S (fieldC_map fx) (fieldC_map fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Optimized differences of fields. -/
theorem fieldC_opt_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m)
    {name : String} {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom name) x y (.map S) = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy
    exact ⟨w, by rw [opt_diff4_eq _ (Or.inl rfl)]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy
    exact ⟨w, by rw [opt_diff4_eq _ (Or.inr (Or.inl rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy
    exact ⟨w, by rw [opt_diff4_eq _ (Or.inr (Or.inr rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.l.opt_diff S (fieldC_list fx) (fieldC_list fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩))), fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.t.opt_diff S (fieldC_tuple fx) (fieldC_tuple fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.m.opt_diff S (fieldC_map fx) (fieldC_map fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Bitmap and atom fields have points. -/
theorem bit_point {x : Term} (h : BitField x) : ∃ i, i < 8 ∧ bitOf x i = Bool.true := by
  obtain ⟨b, rfl, b₁, b₂⟩ := h
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (show b ≠ 0 by omega)
  exact ⟨i, small_bit b₂ hi, by simpa [bitOf_nat] using hi⟩

theorem ptOk_list (ks : Kinds K TF LF MF TV LV MV) {p : Point} (h : LV p.2.2) : PtOkC TV LV MV FV "list" p :=
  ⟨ks.l.resp _ h, by simp, fun _ => h, by simp, by simp, by simp⟩
theorem ptOk_tuple (ks : Kinds K TF LF MF TV LV MV) {p : Point} (h : TV p.2.2) : PtOkC TV LV MV FV "tuple" p :=
  ⟨ks.t.resp _ h, by simp, by simp, fun _ => h, by simp, by simp⟩
theorem ptOk_map (ks : Kinds K TF LF MF TV LV MV) {p : Point} (h : MV p.2.2) : PtOkC TV LV MV FV "map" p :=
  ⟨ks.m.resp _ h, by simp, by simp, by simp, fun _ => h, by simp⟩
theorem ptOk_fun {p : Point} (r : Resp p.2.2) (h : FV p.2.1 p.2.2) : PtOkC TV LV MV FV "fun" p :=
  ⟨r, by simp, by simp, by simp, by simp, fun _ => h⟩

/-- Field emptiness: exact on the structural kinds, never empty on bitmaps and atoms, and complete on functions. -/
theorem fieldC_empty (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {m : Nat} (hm : K ≤ m)
    {name : String} {x : Term} (fx : FieldC Fn TF LF MF name x) (S : List (Term × Term)) (hS : name = "fun" → FS S) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S) = .ok (boolAtom b) ∧
      ∀ N, lh x < N → SafeN N S →
        ((∀ p, PtOkC TV LV MV FV name p → dn name (some x) p = Bool.false) → b = Bool.true) ∧
        (b = Bool.true → ∀ p, PtOkC TV LV MV FV name p → dn name (some x) p = Bool.false) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom], fun N _ _ => ⟨fun h => ?_,
      fun h => by cases h⟩⟩
    obtain ⟨i, lt, hi⟩ := bit_point (fieldC_bitmap fx)
    have := h (i, .nil, fun _ => Bool.true) ⟨resp_const _, fun _ => lt, by simp, by simp, by simp, by simp⟩
    simp [dn_bitmap, hi] at this
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom], fun N _ _ => ⟨fun h => ?_,
      fun h => by cases h⟩⟩
    obtain ⟨⟨p₀, S₀, e, -⟩, q, hq⟩ := fieldC_atom fx
    have := h (0, q, fun _ => Bool.true) ⟨resp_const _, by simp, by simp, by simp, by simp, by simp⟩
    simp [dn_atom, hq] at this
  · obtain ⟨comp, total⟩ := fc.empty S (fieldC_fun fx) (hS rfl) hm
    obtain ⟨b, run, snd⟩ := total hH
    refine ⟨b, run, fun N hx hS' => ⟨fun h => ?_, fun hb p ok => snd N hx hS' hb p ok.1 (ok.2.2.2.2.2 rfl)⟩⟩
    have := (comp N hx hS' fun p r f => h p (ptOk_fun r f)).symm.trans run
    cases b <;> simp_all [boolAtom]
  · obtain ⟨b, run, ex⟩ := ks.l.empty S (fieldC_list fx)
    exact ⟨b, run m hm, fun N hx hS' => ⟨fun h => (ex N hx hS').mpr fun p v => h p (ptOk_list ks v),
      fun hb p ok => (ex N hx hS').mp hb p (ok.2.2.1 rfl)⟩⟩
  · obtain ⟨b, run, ex⟩ := ks.t.empty S (fieldC_tuple fx)
    exact ⟨b, run m hm, fun N hx hS' => ⟨fun h => (ex N hx hS').mpr fun p v => h p (ptOk_tuple ks v),
      fun hb p ok => (ex N hx hS').mp hb p (ok.2.2.2.1 rfl)⟩⟩
  · obtain ⟨b, run, ex⟩ := ks.m.empty S (fieldC_map fx)
    exact ⟨b, run m hm, fun N hx hS' => ⟨fun h => (ex N hx hS').mpr fun p v => h p (ptOk_map ks v),
      fun hb p ok => (ex N hx hS').mp hb p (ok.2.2.2.2.1 rfl)⟩⟩

/-- Fields with no points are checked empty. -/
theorem fieldC_empty_none (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K ≤ m) {name : String}
    {x : Term} (fx : FieldC Fn TF LF MF name x) (hS : name = "fun" → FS [])
    (h : ∀ p, PtOkC TV LV MV FV name p → dn name (some x) p = Bool.false) :
    Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map []) = .ok (.atom "true") := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨i, lt, hi⟩ := bit_point (fieldC_bitmap fx)
    have := h (i, .nil, fun _ => Bool.true) ⟨resp_const _, fun _ => lt, by simp, by simp, by simp, by simp⟩
    simp [dn_bitmap, hi] at this
  · obtain ⟨⟨p₀, S₀, e, -⟩, q, hq⟩ := fieldC_atom fx
    have := h (0, q, fun _ => Bool.true) ⟨resp_const _, by simp, by simp, by simp, by simp, by simp⟩
    simp [dn_atom, hq] at this
  · exact (fc.empty [] (fieldC_fun fx) (hS rfl) hm).1 (lh x + 1) (by omega) (safeN_nil _)
      fun p r f => h p (ptOk_fun r f)
  · obtain ⟨b, run, ex⟩ := ks.l.empty [] (fieldC_list fx)
    have := (ex (lh x + 1) (by omega) (safeN_nil _)).mpr fun p v => h p (ptOk_list ks v)
    subst this; exact run m hm
  · obtain ⟨b, run, ex⟩ := ks.t.empty [] (fieldC_tuple fx)
    have := (ex (lh x + 1) (by omega) (safeN_nil _)).mpr fun p v => h p (ptOk_tuple ks v)
    subst this; exact run m hm
  · obtain ⟨b, run, ex⟩ := ks.m.empty [] (fieldC_map fx)
    have := (ex (lh x + 1) (by omega) (safeN_nil _)).mpr fun p v => h p (ptOk_map ks v)
    subst this; exact run m hm

end

end Elixir.STTDescrProofsTest.Nest
