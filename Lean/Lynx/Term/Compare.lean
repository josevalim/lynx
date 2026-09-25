module

public import Lynx.Term.DataTypes
public import Lynx.Term.Bitstring
import all Lynx.Term.FiniteFloat

public section

/-! Erlang term comparison and semantic equality. Sorted map views and termination
scaffolding are private implementation details of this module. -/

/-! Temporary sorted bindings for map comparison. Keys and values retain their
original representation; only the supplied key comparator is used to sort and
resolve shadowing. -/
namespace Lynx.Term.Compare

variable {α β : Type}

private def mapViewLookup (cmp : α → α → Ordering) (xs : List (α × α)) (q : α) : Option α :=
  (xs.find? fun e => decide (cmp q e.1 = .eq)).map Prod.snd

private def mapViewInsert (cmp : α → α → Ordering) (e : α × α) : List (α × α) → List (α × α)
  | [] => [e]
  | p :: xs => match cmp e.1 p.1 with
    | .eq => e :: xs
    | .lt => e :: p :: xs
    | .gt => p :: mapViewInsert cmp e xs

private def mapView (cmp : α → α → Ordering) : List (α × α) → List (α × α)
  | [] => []
  | e :: xs => mapViewInsert cmp e (mapView cmp xs)

private def compareOn (cmp : β → β → Ordering) (f : α → β) (a b : α) := cmp (f a) (f b)

private instance (cmp : β → β → Ordering) (f : α → β) [Std.TransCmp cmp] : Std.TransCmp (compareOn cmp f) where
  eq_swap := by intros; exact Std.OrientedCmp.eq_swap (cmp := cmp)
  isLE_trans := by intros; exact Std.TransCmp.isLE_trans (cmp := cmp) ‹_› ‹_›

private def ratCompare (a b : Rat) : Ordering := compareOfLessAndEq a b

private theorem rat_lt_trans {a b c : Rat} (hab : a < b) (hbc : b < c) : a < c := by
  rw [Rat.lt_iff_le_and_not_ge]
  refine ⟨Rat.le_trans (Rat.le_of_lt hab) (Rat.le_of_lt hbc), ?_⟩
  intro hca
  have hba := Rat.le_trans (Rat.le_of_lt hbc) hca
  exact (Rat.lt_iff_le_and_not_ge.mp hab).2 hba

private theorem ratCompare_isLE_iff (a b : Rat) : (ratCompare a b).isLE ↔ a ≤ b := by
  rw [Rat.le_iff_lt_or_eq]
  by_cases h : a < b
  · simp [ratCompare, compareOfLessAndEq, h]
  · by_cases e : a = b <;> simp [ratCompare, compareOfLessAndEq, h, e]

@[simp] private theorem ratCompare_eq_iff (a b : Rat) : ratCompare a b = .eq ↔ a = b := by
  by_cases h : a < b
  · simp [ratCompare, compareOfLessAndEq, h, Rat.ne_of_lt h]
  · simp [ratCompare, compareOfLessAndEq, h]

private instance : Std.TransCmp ratCompare where
  eq_swap := by
    intro a b
    by_cases hab : a < b
    · have hba : ¬b < a := fun h => Rat.lt_irrefl (rat_lt_trans hab h)
      have hne : a ≠ b := Rat.ne_of_lt hab
      simp [ratCompare, compareOfLessAndEq, hab, hba, hne.symm]
    · by_cases hba : b < a
      · have hne : a ≠ b := Rat.ne_of_gt hba
        simp [ratCompare, compareOfLessAndEq, hab, hba, hne]
      · have eq : a = b := Rat.le_antisymm (Rat.not_lt.mp hba) (Rat.not_lt.mp hab)
        subst b
        simp [ratCompare, compareOfLessAndEq, Rat.lt_irrefl]
  isLE_trans := by
    intro a b c ab bc
    exact (ratCompare_isLE_iff a c).mpr
      (Rat.le_trans ((ratCompare_isLE_iff a b).mp ab) ((ratCompare_isLE_iff b c).mp bc))

/-- Exact float ordering is numeric first and uses the representation only to
distinguish numerically equal encodings, notably positive and negative zero. -/
private def exactFloatCompareSlow (a b : FiniteFloat) : Ordering :=
  compareLex (compareOn ratCompare FiniteFloat.toRat)
    (compareLex (compareOn Ord.compare (fun value => !value.negative))
      (compareLex (compareOn Ord.compare FiniteFloat.exponent)
        (compareOn Ord.compare FiniteFloat.fraction))) a b

private instance : Std.TransCmp exactFloatCompareSlow :=
  inferInstanceAs (Std.TransCmp (compareLex _ _))

@[simp] private theorem exactFloatCompareSlow_eq_iff (a b : FiniteFloat) :
    exactFloatCompareSlow a b = .eq ↔ a = b := by
  simp only [exactFloatCompareSlow, compareLex, compareOn, Ordering.then_eq_eq,
    ratCompare_eq_iff, Std.compare_eq_iff_eq]
  constructor
  · rintro ⟨_, sign, exponent, fraction⟩
    cases a with
    | mk anegative aexponent afraction =>
      cases b with
      | mk bnegative bexponent bfraction =>
        cases anegative <;> cases bnegative <;> simp_all
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Avoid decoding the binary64 value when the representations are already equal. -/
private def exactFloatCompare (a b : FiniteFloat) : Ordering :=
  if a = b then .eq else exactFloatCompareSlow a b

private theorem exactFloatCompare_eq_slow (a b : FiniteFloat) :
    exactFloatCompare a b = exactFloatCompareSlow a b := by
  simp only [exactFloatCompare]
  split
  · rename_i equal
    subst b
    exact (Std.ReflCmp.compare_self (cmp := exactFloatCompareSlow)).symm
  · rfl

private instance : Std.TransCmp exactFloatCompare where
  eq_swap := by
    intro a b
    rw [exactFloatCompare_eq_slow, exactFloatCompare_eq_slow]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c ab bc
    rw [exactFloatCompare_eq_slow] at ab bc ⊢
    exact Std.TransCmp.isLE_trans ab bc

@[simp] private theorem exactFloatCompare_eq_iff (a b : FiniteFloat) :
    exactFloatCompare a b = .eq ↔ a = b := by
  rw [exactFloatCompare_eq_slow]
  exact exactFloatCompareSlow_eq_iff a b

private def compareMapViews (keyCmp valueCmp : α → α → Ordering) :
    List (α × α) → List (α × α) → Ordering :=
  compareLex (compareOn Ord.compare List.length)
    (compareLex (compareOn (List.compareLex keyCmp) (List.map Prod.fst))
      (compareOn (List.compareLex valueCmp) (List.map Prod.snd)))

private instance (keyCmp valueCmp : α → α → Ordering)
    [Std.TransCmp keyCmp] [Std.TransCmp valueCmp] :
    Std.TransCmp (compareMapViews keyCmp valueCmp) :=
  inferInstanceAs (Std.TransCmp (compareLex _ _))

@[simp] private theorem mapViewInsert_map (cmp : β → β → Ordering) (f : α → β) (e : α × α) (xs : List (α × α)) :
    (mapViewInsert (fun a b => cmp (f a) (f b)) e xs).map (Prod.map f f) =
      mapViewInsert cmp (Prod.map f f e) (xs.map (Prod.map f f)) := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simp only [mapViewInsert, List.map_cons]; split <;> simp_all

@[simp] private theorem mapView_map (cmp : β → β → Ordering) (f : α → β) (xs : List (α × α)) :
    (mapView (fun a b => cmp (f a) (f b)) xs).map (Prod.map f f) =
      mapView cmp (xs.map (Prod.map f f)) := by
  induction xs <;> simp_all [mapView]

@[simp] private theorem lex_map (cmp : β → β → Ordering) (f : α → β) (xs ys : List α) :
    List.compareLex cmp (xs.map f) (ys.map f) =
      List.compareLex (fun a b => cmp (f a) (f b)) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> simp_all [List.compareLex_cons_cons, List.compareLex_cons_nil]

@[simp] private theorem compareMapViews_map (keyCmp valueCmp : β → β → Ordering)
    (f : α → β) (xs ys : List (α × α)) :
    compareMapViews keyCmp valueCmp (xs.map (Prod.map f f)) (ys.map (Prod.map f f)) =
      compareMapViews (fun a b => keyCmp (f a) (f b))
        (fun a b => valueCmp (f a) (f b)) xs ys := by
  simp [compareMapViews, compareLex, compareOn, List.map_map, ← lex_map, Function.comp_def, Prod.map]

end Lynx.Term.Compare

/-! ## Recursive comparison -/

namespace Lynx.Term.Compare

/-- One comparison step. `exact` controls whether integer and float types are
distinct. Map keys always use the exact child comparator. -/
private def compareStep (exact : Bool) (cmp exactCmp : Term → Term → Ordering) :
    Term → Term → Ordering
  | .integer a, .integer b => if exact then Ord.compare a b else ratCompare a b
  | .integer a, .float b => if exact then .lt else ratCompare a b.toRat
  | .float a, .integer b => if exact then .gt else ratCompare a.toRat b
  | .float a, .float b => if exact then exactFloatCompare a b else ratCompare a.toRat b.toRat
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .float _, _ => .lt
  | _, .float _ => .gt
  | .atom a, .atom b => Ord.compare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .function id arity, .function otherId otherArity =>
    (Ord.compare id otherId).then (Ord.compare arity otherArity)
  | .function _ _, _ => .lt
  | _, .function _ _ => .gt
  | .pid a, .pid b => Ord.compare a b
  | .pid _, _ => .lt
  | _, .pid _ => .gt
  | .tuple a, .tuple b =>
    (Ord.compare a.size b.size).then (List.compareLex cmp a.toList b.toList)
  | .tuple _, _ => .lt
  | _, .tuple _ => .gt
  | .map a, .map b =>
      compareMapViews exactCmp cmp (mapView exactCmp a) (mapView exactCmp b)
  | .map _, _ => .lt
  | _, .map _ => .gt
  | .nil, .nil => .eq
  | .nil, .cons _ _ => .lt
  | .cons _ _, .nil => .gt
  | .cons a as, .cons b bs => (cmp a b).then (cmp as bs)
  | .bitstring a ab, .bitstring b bb =>
    List.compareLex Ord.compare (Bitstring.toBits a ab) (Bitstring.toBits b bb)
  | .bitstring _ _, _ => .gt
  | _, .bitstring _ _ => .lt

private abbrev Child (n : Nat) := {t : Term // sizeOf t < n}

private def boundedList (n : Nat) (xs : List Term) (h : ∀ x ∈ xs, sizeOf x < n) : List (Child n) :=
  xs.attachWith (fun x => sizeOf x < n) h

private def boundedEntries (n : Nat) (xs : List (Term × Term))
    (h : ∀ k v, (k,v) ∈ xs → sizeOf k < n ∧ sizeOf v < n) : List (Child n × Child n) :=
  xs.attach.map fun e => (⟨e.val.1, (h _ _ e.property).1⟩, ⟨e.val.2, (h _ _ e.property).2⟩)

@[simp] private theorem boundedList_val (n xs h) : (boundedList n xs h).map Subtype.val = xs := by
  exact List.attachWith_map_subtype_val h
@[simp] private theorem boundedEntries_val (n xs h) :
    (boundedEntries n xs h).map (Prod.map Subtype.val Subtype.val) = xs := by
  simp only [boundedEntries, List.map_map, Function.comp_def, Prod.map]
  change xs.attach.map Subtype.val = xs
  exact List.attach_map_subtype_val xs

private theorem tuple_child {n : Nat} {xs : Array Term} (h : sizeOf (Term.tuple xs) ≤ n)
    (x : Term) (hx : x ∈ xs.toList) : sizeOf x < n := by
  have := Array.sizeOf_lt_of_mem (by simpa using hx : x ∈ xs)
  simp only [Term.tuple.sizeOf_spec] at h
  omega

private theorem map_child {n : Nat} {xs : List (Term × Term)} (h : sizeOf (Term.map xs) ≤ n)
    (k v : Term) (hx : (k,v) ∈ xs) : sizeOf k < n ∧ sizeOf v < n := by
  have := List.sizeOf_lt_of_mem hx
  simp only [Term.map.sizeOf_spec, Prod.mk.sizeOf_spec] at *
  omega

/-- The bound and membership witnesses are used only in types and proofs. -/
private def boundedStep (exact : Bool) (n : Nat) (cmp exactCmp : Child n → Child n → Ordering)
    (a b : Term) (ha : sizeOf a ≤ n) (hb : sizeOf b ≤ n) : Ordering :=
  match a, b with
  | .integer a, .integer b => if exact then Ord.compare a b else ratCompare a b
  | .integer a, .float b => if exact then .lt else ratCompare a b.toRat
  | .float a, .integer b => if exact then .gt else ratCompare a.toRat b
  | .float a, .float b => if exact then exactFloatCompare a b else ratCompare a.toRat b.toRat
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .float _, _ => .lt
  | _, .float _ => .gt
  | .atom a, .atom b => Ord.compare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .function id arity, .function otherId otherArity =>
    (Ord.compare id otherId).then (Ord.compare arity otherArity)
  | .function _ _, _ => .lt
  | _, .function _ _ => .gt
  | .pid a, .pid b => Ord.compare a b
  | .pid _, _ => .lt
  | _, .pid _ => .gt
  | .tuple a, .tuple b =>
    (Ord.compare a.size b.size).then
      (List.compareLex cmp (boundedList n a.toList (tuple_child ha))
        (boundedList n b.toList (tuple_child hb)))
  | .tuple _, _ => .lt
  | _, .tuple _ => .gt
  | .map a, .map b =>
    compareMapViews exactCmp cmp
      (mapView exactCmp (boundedEntries n a (map_child ha)))
      (mapView exactCmp (boundedEntries n b (map_child hb)))
  | .map _, _ => .lt
  | _, .map _ => .gt
  | .nil, .nil => .eq
  | .nil, .cons _ _ => .lt
  | .cons _ _, .nil => .gt
  | .cons a as, .cons b bs =>
    (cmp ⟨a, by simp only [Term.cons.sizeOf_spec] at ha; omega⟩
      ⟨b, by simp only [Term.cons.sizeOf_spec] at hb; omega⟩).then
      (cmp ⟨as, by simp only [Term.cons.sizeOf_spec] at ha; omega⟩
        ⟨bs, by simp only [Term.cons.sizeOf_spec] at hb; omega⟩)
  | .bitstring a ab, .bitstring b bb =>
    List.compareLex Ord.compare (Bitstring.toBits a ab) (Bitstring.toBits b bb)
  | .bitstring _ _, _ => .gt
  | _, .bitstring _ _ => .lt

private theorem boundedStep_eq (exact : Bool) (n : Nat)
    (cmp exactCmp : Term → Term → Ordering) (a b : Term)
    (ha : sizeOf a ≤ n) (hb : sizeOf b ≤ n) :
    boundedStep exact n (fun a b => cmp a.val b.val) (fun a b => exactCmp a.val b.val)
      a b ha hb = compareStep exact cmp exactCmp a b := by
  cases a <;> cases b <;> simp only [boundedStep, compareStep]
  all_goals try rfl
  · rw [← lex_map cmp Subtype.val, boundedList_val, boundedList_val]
  · rw [← compareMapViews_map exactCmp cmp Subtype.val, mapView_map, mapView_map,
      boundedEntries_val, boundedEntries_val]

end Lynx.Term.Compare

namespace Lynx.Term

/-- Erlang comparison, recursing only into children needed to decide the result.
Map comparison resolves shadowing and sorts outer bindings, without rebuilding
nested terms. The termination bound is erased from executable code. -/
@[semireducible] def exactCompare (a b : Term) : Ordering :=
  Compare.boundedStep true (max (sizeOf a) (sizeOf b))
    (fun x y => exactCompare x.val y.val) (fun x y => exactCompare x.val y.val)
    a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)
termination_by max (sizeOf a) (sizeOf b)
decreasing_by all_goals exact Nat.max_lt.mpr ⟨x.property, y.property⟩

private theorem exactCompare_eq_step (a b : Term) :
    exactCompare a b = Compare.compareStep true exactCompare exactCompare a b := by
  rw [exactCompare]
  exact Compare.boundedStep_eq _ _ _ _ _ _ _ _

end Lynx.Term

/-! ## Ordering laws -/

namespace Lynx.Term.Compare

private instance (exact : Bool) (cmp exactCmp : Term → Term → Ordering)
    [Std.TransCmp cmp] [Std.TransCmp exactCmp] :
    Std.TransCmp (compareStep exact cmp exactCmp) where
  eq_swap := by
    intro a b
    cases exact <;> cases a <;> cases b <;> simp only [compareStep, Bool.false_eq_true,
      if_false, if_true, Ordering.swap_then,
      Ordering.swap_eq, Ordering.swap_lt, Ordering.swap_gt]
    all_goals try rfl
    all_goals first
      | exact Std.OrientedCmp.eq_swap
      | (congr 1 <;> exact Std.OrientedCmp.eq_swap)
  isLE_trans := by
    intro a b c ab bc
    cases exact <;> cases a <;> cases b <;> cases c <;>
      simp only [compareStep, Ordering.isLE_lt, Ordering.isLE_eq, Ordering.isLE_gt,
        Bool.false_eq_true, if_false, if_true] at ab bc ⊢
    all_goals try contradiction
    all_goals try trivial
    all_goals try exact Std.TransCmp.isLE_trans ab bc
    case false.function.function.function aid arity bid barity cid carity =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn Ord.compare Prod.fst) (compareOn Ord.compare Prod.snd))
        (a := (aid,arity)) (b := (bid,barity)) (c := (cid,carity)) ab bc
    case true.function.function.function aid arity bid barity cid carity =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn Ord.compare Prod.fst) (compareOn Ord.compare Prod.snd))
        (a := (aid,arity)) (b := (bid,barity)) (c := (cid,carity)) ab bc
    case false.tuple.tuple.tuple a b c =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn Ord.compare Array.size) (compareOn (List.compareLex cmp) Array.toList)) ab bc
    case true.tuple.tuple.tuple a b c =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn Ord.compare Array.size) (compareOn (List.compareLex cmp) Array.toList)) ab bc
    case false.cons.cons.cons ah ats bh bt ch ct =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn cmp Prod.fst) (compareOn cmp Prod.snd))
        (a := (ah,ats)) (b := (bh,bt)) (c := (ch,ct)) ab bc
    case true.cons.cons.cons ah ats bh bt ch ct =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn cmp Prod.fst) (compareOn cmp Prod.snd))
        (a := (ah,ats)) (b := (bh,bt)) (c := (ch,ct)) ab bc

/-- Finite approximations used only to prove ordering laws. Executable comparison
uses well-founded recursion, not a runtime depth counter. -/
private def approximation : Nat → Term → Term → Ordering
  | 0 => fun _ _ => .eq
  | n + 1 => compareStep true (approximation n) (approximation n)

private instance approximation_trans (n : Nat) : Std.TransCmp (approximation n) := by
  induction n with
  | zero => exact { eq_swap := by intros; rfl, isLE_trans := by intros; rfl }
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Std.TransCmp (compareStep true (approximation n) (approximation n)))

private theorem exactCompare_eq_approximation (n : Nat) (a b : Term)
    (h : max (sizeOf a) (sizeOf b) ≤ n) : Term.exactCompare a b = approximation n a b := by
  induction n generalizing a b with
  | zero => cases a <;> simp_all <;> omega
  | succ n ih =>
    rw [Term.exactCompare, approximation,
      ← boundedStep_eq true (max (sizeOf a) (sizeOf b)) (approximation n) (approximation n) a b
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
    congr 1 <;> funext x y <;>
      exact ih x.val y.val (by have := x.property; have := y.property; omega)

end Lynx.Term.Compare

namespace Lynx.Term

@[simp] theorem exactCompare_self (a : Term) : exactCompare a a = .eq := by
  rw [Compare.exactCompare_eq_approximation (sizeOf a) a a (by simp)]
  exact Std.ReflCmp.compare_self

theorem exactCompare_swap (a b : Term) : exactCompare a b = (exactCompare b a).swap := by
  let n := max (sizeOf a) (sizeOf b)
  rw [Compare.exactCompare_eq_approximation n a b (by omega),
    Compare.exactCompare_eq_approximation n b a (by omega)]
  exact Std.OrientedCmp.eq_swap

theorem exactCompare_le_trans (a b c : Term)
    (ab : (exactCompare a b).isLE) (bc : (exactCompare b c).isLE) : (exactCompare a c).isLE := by
  let n := max (max (sizeOf a) (sizeOf b)) (sizeOf c)
  rw [Compare.exactCompare_eq_approximation n a b (by omega)] at ab
  rw [Compare.exactCompare_eq_approximation n b c (by omega)] at bc
  rw [Compare.exactCompare_eq_approximation n a c (by omega)]
  exact Std.TransCmp.isLE_trans ab bc

theorem exactCompare_le_total (a b : Term) : (exactCompare a b).isLE ∨ (exactCompare b a).isLE := by
  rw [exactCompare_swap b a]
  cases exactCompare a b <;> decide

instance : Std.TransCmp exactCompare where
  eq_swap := exactCompare_swap _ _
  isLE_trans := exactCompare_le_trans _ _ _

end Lynx.Term

/-! ## Numeric comparison

Ordinary Erlang comparison coerces integers and floats into one numeric domain.
Map keys remain exact terms even under ordinary comparison. -/

namespace Lynx.Term

/-- Erlang term comparison with numeric coercion between integers and floats.
Map keys retain their exact types. -/
@[semireducible] def compare (a b : Term) : Ordering :=
  Compare.boundedStep false (max (sizeOf a) (sizeOf b))
    (fun x y => compare x.val y.val) (fun x y => exactCompare x.val y.val)
    a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)
termination_by max (sizeOf a) (sizeOf b)
decreasing_by exact Nat.max_lt.mpr ⟨x.property, y.property⟩

private theorem compare_eq_step (a b : Term) :
    compare a b = Compare.compareStep false compare exactCompare a b := by
  rw [compare]
  exact Compare.boundedStep_eq _ _ _ _ _ _ _ _

end Lynx.Term

namespace Lynx.Term.Compare

private def numericApproximation : Nat → Term → Term → Ordering
  | 0 => fun _ _ => .eq
  | n + 1 => compareStep false (numericApproximation n) exactCompare

private instance numericApproximation_trans (n : Nat) :
    Std.TransCmp (numericApproximation n) := by
  induction n with
  | zero => exact { eq_swap := by intros; rfl, isLE_trans := by intros; rfl }
  | succ n ih =>
    letI := ih
    exact inferInstanceAs
      (Std.TransCmp (compareStep false (numericApproximation n) exactCompare))

private theorem compare_eq_approximation (n : Nat) (a b : Term)
    (h : max (sizeOf a) (sizeOf b) ≤ n) : Term.compare a b = numericApproximation n a b := by
  induction n generalizing a b with
  | zero => cases a <;> simp_all <;> omega
  | succ n ih =>
    rw [Term.compare, numericApproximation,
      ← boundedStep_eq false (max (sizeOf a) (sizeOf b)) (numericApproximation n)
        exactCompare a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
    congr 1
    funext x y
    exact ih x.val y.val (by have := x.property; have := y.property; omega)

end Lynx.Term.Compare

namespace Lynx.Term

@[simp] theorem compare_self (a : Term) : compare a a = .eq := by
  rw [Compare.compare_eq_approximation (sizeOf a) a a (by simp)]
  exact Std.ReflCmp.compare_self

theorem compare_swap (a b : Term) : compare a b = (compare b a).swap := by
  let n := max (sizeOf a) (sizeOf b)
  rw [Compare.compare_eq_approximation n a b (by omega),
    Compare.compare_eq_approximation n b a (by omega)]
  exact Std.OrientedCmp.eq_swap

theorem compare_le_trans (a b c : Term)
    (ab : (compare a b).isLE) (bc : (compare b c).isLE) : (compare a c).isLE := by
  let n := max (max (sizeOf a) (sizeOf b)) (sizeOf c)
  rw [Compare.compare_eq_approximation n a b (by omega)] at ab
  rw [Compare.compare_eq_approximation n b c (by omega)] at bc
  rw [Compare.compare_eq_approximation n a c (by omega)]
  exact Std.TransCmp.isLE_trans ab bc

theorem compare_le_total (a b : Term) : (compare a b).isLE ∨ (compare b a).isLE := by
  rw [compare_swap b a]
  cases compare a b <;> decide

instance : Std.TransCmp compare where
  eq_swap := compare_swap _ _
  isLE_trans := compare_le_trans _ _ _

end Lynx.Term

/-! ## Exact equality -/

namespace Lynx.Term

@[simp] theorem exactCompare_eq_nil (a : Term) : exactCompare a .nil = .eq ↔ a = .nil := by
  cases a <;> rw [exactCompare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem nil_exactCompare_eq (a : Term) : exactCompare .nil a = .eq ↔ a = .nil := by
  rw [exactCompare_swap, Ordering.swap_eq_eq]
  exact exactCompare_eq_nil a
@[simp] theorem exactCompare_eq_integer (a : Term) (n : Int) :
    exactCompare a (.integer n) = .eq ↔ a = .integer n := by
  cases a <;> rw [exactCompare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem integer_exactCompare_eq (n : Int) (a : Term) :
    exactCompare (.integer n) a = .eq ↔ a = .integer n := by
  rw [exactCompare_swap, Ordering.swap_eq_eq]
  exact exactCompare_eq_integer a n
@[simp] theorem exactCompare_eq_float (a : Term) (n : FiniteFloat) :
    exactCompare a (.float n) = .eq ↔ a = .float n := by
  cases a <;> rw [exactCompare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem float_exactCompare_eq (n : FiniteFloat) (a : Term) :
    exactCompare (.float n) a = .eq ↔ a = .float n := by
  rw [exactCompare_swap, Ordering.swap_eq_eq]
  exact exactCompare_eq_float a n
@[simp] theorem exactCompare_eq_atom (a : Term) (s : String) :
    exactCompare a (.atom s) = .eq ↔ a = .atom s := by
  cases a <;> rw [exactCompare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem atom_exactCompare_eq (s : String) (a : Term) :
    exactCompare (.atom s) a = .eq ↔ a = .atom s := by
  rw [exactCompare_swap, Ordering.swap_eq_eq]
  exact exactCompare_eq_atom a s
@[simp] theorem exactCompare_eq_function (a : Term) (id arity : Nat) :
    exactCompare a (.function id arity) = .eq ↔ a = .function id arity := by
  cases a <;> rw [exactCompare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem function_exactCompare_eq (id arity : Nat) (a : Term) :
    exactCompare (.function id arity) a = .eq ↔ a = .function id arity := by
  rw [exactCompare_swap, Ordering.swap_eq_eq]
  exact exactCompare_eq_function a id arity
@[simp] theorem exactCompare_eq_pid (a : Term) (pid : PID) :
    exactCompare a (.pid pid) = .eq ↔ a = .pid pid := by
  cases a <;> rw [exactCompare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem pid_exactCompare_eq (pid : PID) (a : Term) :
    exactCompare (.pid pid) a = .eq ↔ a = .pid pid := by
  rw [exactCompare_swap, Ordering.swap_eq_eq]
  exact exactCompare_eq_pid a pid

end Lynx.Term

/-! ## Numeric equality -/

namespace Lynx.Term

@[simp] theorem compare_eq_nil (a : Term) : compare a .nil = .eq ↔ a = .nil := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem nil_compare_eq (a : Term) : compare .nil a = .eq ↔ a = .nil := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_nil a
theorem compare_eq_integer (a : Term) (n : Int) :
    compare a (.integer n) = .eq ↔
      a = .integer n ∨ ∃ float, a = .float float ∧ float.toRat = n := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
theorem integer_compare_eq (n : Int) (a : Term) :
    compare (.integer n) a = .eq ↔
      a = .integer n ∨ ∃ float, a = .float float ∧ float.toRat = n := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_integer a n
theorem compare_eq_float (a : Term) (n : FiniteFloat) :
    compare a (.float n) = .eq ↔
      (∃ float, a = .float float ∧ float.toRat = n.toRat) ∨
      ∃ integer : Int, a = .integer integer ∧ integer = n.toRat := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
theorem float_compare_eq (n : FiniteFloat) (a : Term) :
    compare (.float n) a = .eq ↔
      (∃ float, a = .float float ∧ float.toRat = n.toRat) ∨
      ∃ integer : Int, a = .integer integer ∧ integer = n.toRat := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_float a n
@[simp] theorem integer_compare_integer_eq (a b : Int) :
    compare (.integer a) (.integer b) = .eq ↔ a = b := by
  rw [integer_compare_eq]
  simp [eq_comm]
@[simp] theorem integer_compare_float_eq (integer : Int) (float : FiniteFloat) :
    compare (.integer integer) (.float float) = .eq ↔ integer = float.toRat := by
  rw [integer_compare_eq]
  simp [eq_comm]
@[simp] theorem float_compare_integer_eq (float : FiniteFloat) (integer : Int) :
    compare (.float float) (.integer integer) = .eq ↔ float.toRat = integer := by
  rw [compare_eq_integer]
  simp
@[simp] theorem float_compare_float_eq (a b : FiniteFloat) :
    compare (.float a) (.float b) = .eq ↔ a.toRat = b.toRat := by
  rw [float_compare_eq]
  simp [eq_comm]
@[simp] theorem compare_eq_atom (a : Term) (s : String) :
    compare a (.atom s) = .eq ↔ a = .atom s := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem atom_compare_eq (s : String) (a : Term) :
    compare (.atom s) a = .eq ↔ a = .atom s := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_atom a s
@[simp] theorem compare_eq_function (a : Term) (id arity : Nat) :
    compare a (.function id arity) = .eq ↔ a = .function id arity := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem function_compare_eq (id arity : Nat) (a : Term) :
    compare (.function id arity) a = .eq ↔ a = .function id arity := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_function a id arity
@[simp] theorem compare_eq_pid (a : Term) (pid : PID) :
    compare a (.pid pid) = .eq ↔ a = .pid pid := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem pid_compare_eq (pid : PID) (a : Term) :
    compare (.pid pid) a = .eq ↔ a = .pid pid := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_pid a pid

end Lynx.Term

namespace Lynx

/-- Executable semantic equality. Lean `=` still compares representations. -/
instance : BEq Term := ⟨fun a b => decide (Term.compare a b = .eq)⟩

@[simp] theorem Term.beq_iff_compare_eq (a b : Term) :
    (a == b) = true ↔ Term.compare a b = .eq := by
  change decide (Term.compare a b = .eq) = true ↔ _
  simp

instance : EquivBEq Term where
  rfl := by intro a; exact (Term.beq_iff_compare_eq a a).mpr (Term.compare_self a)
  symm := by
    intro a b h
    exact (Term.beq_iff_compare_eq b a).mpr
      (Std.OrientedCmp.eq_symm ((Term.beq_iff_compare_eq a b).mp h))
  trans := by
    intro a b c h h'
    exact (Term.beq_iff_compare_eq a c).mpr
      (Std.TransCmp.eq_trans ((Term.beq_iff_compare_eq a b).mp h)
        ((Term.beq_iff_compare_eq b c).mp h'))

end Lynx

namespace Lynx.Term

theorem compare_congr {a b c d : Term}
    (ha : compare a b = .eq) (hb : compare c d = .eq) :
    compare a c = compare b d :=
  (Std.TransCmp.congr_left ha).trans (Std.TransCmp.congr_right hb)

/-- Non-strict Erlang term order, used in mathematical specifications. -/
abbrev le (a b : Term) : Prop := (compare a b).isLE

end Lynx.Term

/-! ## Map extensionality through first-binding lookups -/

namespace Lynx.Term.Compare
variable {α : Type} (cmp : α → α → Ordering)

private def MapViewSorted (xs : List (α × α)) : Prop := xs.Pairwise (fun a b => cmp a.1 b.1 = .lt)

@[simp] private theorem mapViewLookup_nil (q : α) : mapViewLookup cmp [] q = none := rfl

@[simp] private theorem mapViewLookup_cons (e : α × α) (xs : List (α × α)) (q : α) :
    mapViewLookup cmp (e :: xs) q = if cmp q e.1 = .eq then some e.2 else mapViewLookup cmp xs q := by
  by_cases h : cmp q e.1 = .eq <;> simp [mapViewLookup, List.find?, h]

@[simp] private theorem mapViewSorted_nil : MapViewSorted cmp [] := by simp [MapViewSorted]
@[simp] private theorem mapViewSorted_cons (e : α × α) (xs : List (α × α)) :
    MapViewSorted cmp (e :: xs) ↔ (∀ p ∈ xs, cmp e.1 p.1 = .lt) ∧ MapViewSorted cmp xs := List.pairwise_cons

private theorem mem_mapViewInsert {xs : List (α × α)} {e p : α × α} (h : p ∈ mapViewInsert cmp e xs) :
    p = e ∨ p ∈ xs := by
  induction xs with
  | nil => simpa [mapViewInsert] using h
  | cons q xs ih =>
    simp only [mapViewInsert] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · exact List.mem_cons.mp h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

variable [Std.TransCmp cmp]

@[simp] private theorem mapViewSorted_insert (e : α × α) (xs : List (α × α)) (hs : MapViewSorted cmp xs) :
    MapViewSorted cmp (mapViewInsert cmp e xs) := by
  induction xs with
  | nil => simp [mapViewInsert]
  | cons p xs ih =>
    obtain ⟨head,tail⟩ := (mapViewSorted_cons cmp p xs).mp hs
    simp only [mapViewInsert]
    split
    · rename_i eq
      exact (mapViewSorted_cons cmp e xs).mpr ⟨fun q h => by
        rw [Std.TransCmp.congr_left eq]; exact head q h, tail⟩
    · rename_i lt
      apply (mapViewSorted_cons cmp e (p :: xs)).mpr
      refine ⟨?_, hs⟩
      intro q h
      rcases List.mem_cons.mp h with rfl | h
      · exact lt
      · exact Std.TransCmp.lt_trans lt (head q h)
    · rename_i gt
      apply (mapViewSorted_cons cmp p _).mpr
      refine ⟨?_, ih tail⟩
      intro q h
      rcases mem_mapViewInsert cmp h with rfl | h
      · exact Std.OrientedCmp.lt_of_gt gt
      · exact head q h

@[simp] private theorem mapView_sorted (xs : List (α × α)) : MapViewSorted cmp (mapView cmp xs) := by
  induction xs <;> simp_all [mapView]

@[simp] private theorem mapViewLookup_insert (xs : List (α × α)) (e : α × α) (q : α) :
    mapViewLookup cmp (mapViewInsert cmp e xs) q = if cmp q e.1 = .eq then some e.2 else mapViewLookup cmp xs q := by
  induction xs with
  | nil => simp [mapViewInsert, mapViewLookup_cons, mapViewLookup_nil]
  | cons p xs ih =>
    simp only [mapViewInsert]
    split
    · rename_i eq
      by_cases h : cmp q p.1 = .eq <;> simp [mapViewLookup_cons, Std.TransCmp.congr_right (a := q) eq, h]
    · by_cases h : cmp q e.1 = .eq <;> simp [mapViewLookup_cons, h]
    · rename_i gt
      by_cases h : cmp q e.1 = .eq
      · have ne : cmp q p.1 ≠ .eq := by rw [Std.TransCmp.congr_left h, gt]; decide
        simp [mapViewLookup_cons, h, ne, ih]
      · simp [mapViewLookup_cons, h, ih]

@[simp] private theorem mapViewLookup_view (xs : List (α × α)) (q : α) :
    mapViewLookup cmp (mapView cmp xs) q = mapViewLookup cmp xs q := by
  induction xs <;> simp_all [mapView, mapViewLookup_cons, mapViewLookup_nil]

omit [Std.TransCmp cmp] in
private theorem mapViewLookup_absent {xs : List (α × α)} {q : α}
    (h : ∀ e ∈ xs, cmp q e.1 = .lt) : mapViewLookup cmp xs q = none := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    have head := h e (by simp)
    simp [mapViewLookup_cons, head, ih (fun p mem => h p (List.mem_cons_of_mem _ mem))]

/-- Sorted views are extensionally equal with respect to comparator equality;
the stored representatives themselves need not be equal. -/
private theorem compareMapViews_eq_of_lookup (valueCmp : α → α → Ordering)
    [Std.TransCmp valueCmp] (a b : List (α × α))
    (ha : MapViewSorted cmp a) (hb : MapViewSorted cmp b)
    (h : ∀ q, Option.Rel (fun a b => valueCmp a b = .eq)
      (mapViewLookup cmp a q) (mapViewLookup cmp b q)) :
    compareMapViews cmp valueCmp a b = .eq := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons e b => have := h e.1; simp [mapViewLookup_cons, Std.ReflCmp.compare_self] at this
  | cons e a ih =>
    cases b with
    | nil => have := h e.1; simp [mapViewLookup_cons, Std.ReflCmp.compare_self] at this
    | cons f b =>
      obtain ⟨ah,ats⟩ := (mapViewSorted_cons cmp e a).mp ha
      obtain ⟨bh,bt⟩ := (mapViewSorted_cons cmp f b).mp hb
      have keys : cmp e.1 f.1 = .eq := by
        cases eq : cmp e.1 f.1 with
        | eq => rfl
        | lt =>
          have absent : mapViewLookup cmp (f :: b) e.1 = none := mapViewLookup_absent cmp (by
            intro p mem
            rcases List.mem_cons.mp mem with rfl | mem
            · exact eq
            · exact Std.TransCmp.lt_trans eq (bh p mem))
          have := h e.1
          rw [absent] at this
          simp [mapViewLookup_cons, Std.ReflCmp.compare_self] at this
        | gt =>
          have lt := Std.OrientedCmp.lt_of_gt eq
          have absent : mapViewLookup cmp (e :: a) f.1 = none := mapViewLookup_absent cmp (by
            intro p mem
            rcases List.mem_cons.mp mem with rfl | mem
            · exact lt
            · exact Std.TransCmp.lt_trans lt (ah p mem))
          have := h f.1
          rw [absent] at this
          simp [mapViewLookup_cons, Std.ReflCmp.compare_self] at this
      have values : valueCmp e.2 f.2 = .eq := by
        simpa [mapViewLookup_cons, Std.ReflCmp.compare_self, keys] using h e.1
      have tails := ih b ats bt (by
        intro q
        by_cases eq : cmp q e.1 = .eq
        · have aa : mapViewLookup cmp a q = none := mapViewLookup_absent cmp (fun p mem =>
            Std.TransCmp.lt_of_eq_of_lt eq (ah p mem))
          have bb : mapViewLookup cmp b q = none := mapViewLookup_absent cmp (fun p mem =>
            Std.TransCmp.lt_of_eq_of_lt (Std.TransCmp.eq_trans eq keys) (bh p mem))
          simp [aa, bb]
        · simpa [mapViewLookup_cons, eq, ← Std.TransCmp.congr_right (a := q) keys] using h q)
      simp only [compareMapViews, compareLex, compareOn, Ordering.then_eq_eq,
        List.length_cons, List.map_cons, List.compareLex_cons_cons, keys, values,
        Ordering.eq_then, Std.compare_eq_iff_eq, Nat.add_right_cancel_iff] at tails ⊢
      exact tails

end Lynx.Term.Compare

namespace Lynx.Term

/-- Constructor order places every integer before every map. -/
theorem exactCompare_integer_map (n : Int) (entries : List (Term × Term)) :
    exactCompare (.integer n) (.map entries) = .lt := by
  rw [exactCompare_eq_step]
  rfl

/-- Exact comparison keeps integer and float representations distinct. -/
@[simp] theorem exactCompare_integer_float (integer : Int) (float : FiniteFloat) :
    exactCompare (.integer integer) (.float float) = .lt := by
  rw [exactCompare_eq_step]
  rfl

@[simp] theorem exactCompare_float_integer (float : FiniteFloat) (integer : Int) :
    exactCompare (.float float) (.integer integer) = .gt := by
  rw [exactCompare_eq_step]
  rfl

/-- Tuples exactCompare arity before their elements. -/
theorem exactCompare_tuple (a b : Array Term) :
    exactCompare (.tuple a) (.tuple b) =
      (Ord.compare a.size b.size).then (List.compareLex exactCompare a.toList b.toList) := by
  rw [exactCompare_eq_step]
  rfl

/-- Lists exactCompare their heads before their tails. -/
theorem exactCompare_cons (a as b bs : Term) :
    exactCompare (.cons a as) (.cons b bs) = (exactCompare a b).then (exactCompare as bs) := by
  rw [exactCompare_eq_step]
  rfl

/-- A singleton map is larger than the empty map, regardless of its binding. -/
theorem exactCompare_singleton_map_empty (k v : Term) :
    exactCompare (.map [(k,v)]) (.map []) = .gt := by
  rw [exactCompare_eq_step]
  rfl

/-- Singleton maps exactCompare their keys before their values. -/
theorem exactCompare_singleton_map (k v l w : Term) :
    exactCompare (.map [(k,v)]) (.map [(l,w)]) = (exactCompare k l).then (exactCompare v w) := by
  rw [exactCompare_eq_step]
  simp [Compare.compareStep, Compare.mapView, Compare.mapViewInsert, Compare.compareMapViews,
    compareLex, Compare.compareOn,
    List.compareLex_cons_cons, List.compareLex_nil_nil]

/-- Every number precedes every map under ordinary comparison. -/
theorem compare_integer_map (n : Int) (entries : List (Term × Term)) :
    compare (.integer n) (.map entries) = .lt := by
  rw [compare_eq_step]
  rfl

/-- Tuples compare arity before their elements. -/
theorem compare_tuple (a b : Array Term) :
    compare (.tuple a) (.tuple b) =
      (Ord.compare a.size b.size).then (List.compareLex compare a.toList b.toList) := by
  rw [compare_eq_step]
  rfl

/-- Lists compare their heads before their tails. -/
theorem compare_cons (a as b bs : Term) :
    compare (.cons a as) (.cons b bs) = (compare a b).then (compare as bs) := by
  rw [compare_eq_step]
  rfl

/-- A singleton map is larger than the empty map, regardless of its binding. -/
theorem compare_singleton_map_empty (k v : Term) :
    compare (.map [(k,v)]) (.map []) = .gt := by
  rw [compare_eq_step]
  rfl

/-- Singleton maps compare exact keys before ordinarily compared values. -/
theorem compare_singleton_map (k v l w : Term) :
    compare (.map [(k,v)]) (.map [(l,w)]) =
      (exactCompare k l).then (compare v w) := by
  rw [compare_eq_step]
  simp [Compare.compareStep, Compare.mapView, Compare.mapViewInsert, Compare.compareMapViews,
    compareLex, Compare.compareOn, List.compareLex_cons_cons, List.compareLex_nil_nil]

/-- Matching first-binding lookups suffice for semantic map equality. -/
theorem map_compare_eq_of_lookup (a b : List (Term × Term))
    (h : ∀ q, Option.Rel (fun a b => compare a b = .eq)
      ((a.find? fun e => decide (exactCompare q e.1 = .eq)).map Prod.snd)
      ((b.find? fun e => decide (exactCompare q e.1 = .eq)).map Prod.snd)) :
    compare (.map a) (.map b) = .eq := by
  rw [compare_eq_step]
  apply Compare.compareMapViews_eq_of_lookup (cmp := exactCompare) compare _ _
    (Compare.mapView_sorted _ _) (Compare.mapView_sorted _ _)
  intro q
  simp only [Compare.mapViewLookup_view]
  exact h q

end Lynx.Term
