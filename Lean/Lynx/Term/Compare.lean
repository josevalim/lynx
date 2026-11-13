module

public import Lynx.Term.DataTypes
public import Lynx.Term.Bitstring
import Lynx.Term.Eval
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

@[expose] def mapViewInsert (cmp : α → α → Ordering) (e : α × α) : List (α × α) → List (α × α)
  | [] => [e]
  | p :: xs => match cmp e.1 p.1 with
    | .eq => e :: xs
    | .lt => e :: p :: xs
    | .gt => p :: mapViewInsert cmp e xs

@[expose] def mapView (cmp : α → α → Ordering) : List (α × α) → List (α × α)
  | [] => []
  | e :: xs => mapViewInsert cmp e (mapView cmp xs)

@[expose] def compareOn (cmp : β → β → Ordering) (f : α → β) (a b : α) := cmp (f a) (f b)

private instance (cmp : β → β → Ordering) (f : α → β) [Std.TransCmp cmp] : Std.TransCmp (compareOn cmp f) where
  eq_swap := by intros; exact Std.OrientedCmp.eq_swap (cmp := cmp)
  isLE_trans := by intros; exact Std.TransCmp.isLE_trans (cmp := cmp) ‹_› ‹_›

@[expose] def ratCompare (a b : Rat) : Ordering := compareOfLessAndEq a b

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

/-- String order, comparing the characters as lists so that evaluation in the
kernel can decide it. -/
@[expose] def stringCompare (a b : String) : Ordering :=
  compareOfLessAndEq a.toList b.toList

@[simp] private theorem stringCompare_eq (a b : String) : stringCompare a b = Ord.compare a b := by
  show _ = String.compare a b
  rw [Term.string_compare_eq]
  have lt : (a < b) = (a.toList < b.toList) := rfl
  have eq : (a = b) = (a.toList = b.toList) := propext String.toList_inj.symm
  simp only [stringCompare, compareOfLessAndEq, lt, eq]

@[simp] theorem stringCompare_eq_iff (a b : String) : stringCompare a b = .eq ↔ a = b := by
  rw [stringCompare_eq, Std.compare_eq_iff_eq]

private instance : Std.TransCmp stringCompare := by
  have : stringCompare = fun a b => Ord.compare a b :=
    funext fun a => funext fun b => stringCompare_eq a b
  rw [this]
  infer_instance

/-- Exact float ordering is numeric first and uses the representation only to
distinguish numerically equal encodings, notably positive and negative zero. -/
@[expose] def exactFloatCompareSlow (a b : FiniteFloat) : Ordering :=
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

/-- Avoid decoding the binary64 value when the representations are already
equal. The representations are compared field by field, so evaluation in the
kernel does not need the derived decidable equality. -/
@[expose] def exactFloatCompare (a b : FiniteFloat) : Ordering :=
  if a.negative == b.negative && a.exponent.val == b.exponent.val && a.fraction.val == b.fraction.val then
    .eq
  else exactFloatCompareSlow a b

private theorem exactFloatCompare_eq_slow (a b : FiniteFloat) :
    exactFloatCompare a b = exactFloatCompareSlow a b := by
  simp only [exactFloatCompare]
  split
  · rename_i equal
    have : a = b := by
      obtain ⟨negative, exponent, fraction⟩ := a
      obtain ⟨negative', exponent', fraction'⟩ := b
      simp only [Bool.and_eq_true, beq_iff_eq] at equal
      obtain ⟨⟨rfl, same⟩, same'⟩ := equal
      rw [Fin.ext same, Fin.ext same']
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

@[expose] def compareMapViews (keyCmp valueCmp : α → α → Ordering) :
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
distinct. Map keys always use the exact child comparator. Its body is exposed
so evaluation can compare terms. -/
@[expose] def compareStep (exact : Bool) (cmp exactCmp : Term → Term → Ordering) :
    Term → Term → Ordering
  | .integer a, .integer b => if exact then Ord.compare a b else ratCompare a b
  | .integer a, .float b => if exact then .lt else ratCompare a b.toRat
  | .float a, .integer b => if exact then .gt else ratCompare a.toRat b
  | .float a, .float b => if exact then exactFloatCompare a b else ratCompare a.toRat b.toRat
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .float _, _ => .lt
  | _, .float _ => .gt
  | .atom a, .atom b => stringCompare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .reference a, .reference b => Ord.compare a b
  | .reference _, _ => .lt
  | _, .reference _ => .gt
  | .function module name arity captures, .function otherModule otherName otherArity otherCaptures =>
    (stringCompare module otherModule).then ((stringCompare name otherName).then
      ((Ord.compare arity otherArity).then
        (List.compareLex exactCmp captures.toList otherCaptures.toList)))
  | .function _ _ _ _, _ => .lt
  | _, .function _ _ _ _ => .gt
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
  | .bitstring a ab _, .bitstring b bb _ =>
    List.compareLex Ord.compare (Bitstring.toBits a ab) (Bitstring.toBits b bb)
  | .bitstring _ _ _, _ => .gt
  | _, .bitstring _ _ _ => .lt

end Lynx.Term.Compare

namespace Lynx.Term

mutual
/-- How deeply a term nests. Comparing two terms takes a step per level. -/
@[expose] def nesting : Term → Nat
  | .function _ _ _ captures => nestingList captures.toList + 1
  | .tuple elements => nestingList elements.toList + 1
  | .map entries => nestingEntries entries + 1
  | .cons head tail => max (nesting head) (nesting tail) + 1
  | _ => 0
termination_by structural term => term

/-- The deepest of a list of terms. -/
@[expose] def nestingList : List Term → Nat
  | [] => 0
  | term :: rest => max (nesting term) (nestingList rest)
termination_by structural terms => terms

/-- The deepest key or value of a map's bindings. -/
@[expose] def nestingEntries : List (Term × Term) → Nat
  | [] => 0
  | (key, value) :: rest => max (max (nesting key) (nesting value)) (nestingEntries rest)
termination_by structural entries => entries
end

/-- Steps enough to compare two terms. -/
@[expose] def fuel (a b : Term) : Nat := max (nesting a) (nesting b) + 1

/-- Erlang's exact term order, in which integers and floats differ, taking at
most `fuel` steps; `Term.fuel` steps decide it. -/
@[expose] def compareExact : Nat → Term → Term → Ordering
  | 0 => fun _ _ => .eq
  | fuel + 1 => Compare.compareStep true (compareExact fuel) (compareExact fuel)

/-- Erlang's term order, in which integers and floats compare by value, taking
at most `fuel` steps; `Term.fuel` steps decide it. Map keys compare exactly. -/
@[expose] def compare : Nat → Term → Term → Ordering
  | 0 => fun _ _ => .eq
  | fuel + 1 => Compare.compareStep false (compare fuel) (compareExact fuel)

/-! ### Children are less deep -/

private theorem nesting_le_list {term : Term} : ∀ {terms : List Term}, term ∈ terms →
    nesting term ≤ nestingList terms
  | _ :: _, .head _ => by simp only [nestingList]; omega
  | _ :: _, .tail _ mem => by have := nesting_le_list mem; simp only [nestingList]; omega

private theorem nesting_le_entries {key value : Term} : ∀ {entries : List (Term × Term)},
    (key, value) ∈ entries → nesting key ≤ nestingEntries entries ∧ nesting value ≤ nestingEntries entries
  | _ :: _, .head _ => by simp only [nestingEntries]; omega
  | (_, _) :: _, .tail _ mem => by
    have := nesting_le_entries mem; simp only [nestingEntries]; omega

end Lynx.Term

namespace Lynx.Term.Compare

private abbrev Child (n : Nat) := {t : Term // Term.nesting t < n}

private def boundedList (n : Nat) (xs : List Term) (h : ∀ x ∈ xs, Term.nesting x < n) : List (Child n) :=
  xs.attachWith (fun x => Term.nesting x < n) h

private def boundedEntries (n : Nat) (xs : List (Term × Term))
    (h : ∀ k v, (k,v) ∈ xs → Term.nesting k < n ∧ Term.nesting v < n) : List (Child n × Child n) :=
  xs.attach.map fun e => (⟨e.val.1, (h _ _ e.property).1⟩, ⟨e.val.2, (h _ _ e.property).2⟩)

@[simp] private theorem boundedList_val (n xs h) : (boundedList n xs h).map Subtype.val = xs := by
  exact List.attachWith_map_subtype_val h
@[simp] private theorem boundedEntries_val (n xs h) :
    (boundedEntries n xs h).map (Prod.map Subtype.val Subtype.val) = xs := by
  simp only [boundedEntries, List.map_map, Function.comp_def, Prod.map]
  change xs.attach.map Subtype.val = xs
  exact List.attach_map_subtype_val xs

private theorem tuple_child {n : Nat} {xs : Array Term} (h : Term.nesting (Term.tuple xs) ≤ n)
    (x : Term) (hx : x ∈ xs.toList) : Term.nesting x < n := by
  have := Term.nesting_le_list hx
  simp only [Term.nesting] at h
  omega

private theorem function_child {n arity : Nat} {module name : String} {xs : Array Term}
    (h : Term.nesting (Term.function module name arity xs) ≤ n) (x : Term) (hx : x ∈ xs.toList) :
    Term.nesting x < n := by
  have := Term.nesting_le_list hx
  simp only [Term.nesting] at h
  omega

private theorem map_child {n : Nat} {xs : List (Term × Term)} (h : Term.nesting (Term.map xs) ≤ n)
    (k v : Term) (hx : (k,v) ∈ xs) : Term.nesting k < n ∧ Term.nesting v < n := by
  have := Term.nesting_le_entries hx
  simp only [Term.nesting] at h
  omega

/-- The bound and membership witnesses are used only in types and proofs. -/
private def boundedStep (exact : Bool) (n : Nat) (cmp exactCmp : Child n → Child n → Ordering)
    (a b : Term) (ha : Term.nesting a ≤ n) (hb : Term.nesting b ≤ n) : Ordering :=
  match a, b with
  | .integer a, .integer b => if exact then Ord.compare a b else ratCompare a b
  | .integer a, .float b => if exact then .lt else ratCompare a b.toRat
  | .float a, .integer b => if exact then .gt else ratCompare a.toRat b
  | .float a, .float b => if exact then exactFloatCompare a b else ratCompare a.toRat b.toRat
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .float _, _ => .lt
  | _, .float _ => .gt
  | .atom a, .atom b => stringCompare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .reference a, .reference b => Ord.compare a b
  | .reference _, _ => .lt
  | _, .reference _ => .gt
  | .function module name arity captures, .function otherModule otherName otherArity otherCaptures =>
    (stringCompare module otherModule).then ((stringCompare name otherName).then
      ((Ord.compare arity otherArity).then
        (List.compareLex exactCmp (boundedList n captures.toList (function_child ha))
          (boundedList n otherCaptures.toList (function_child hb)))))
  | .function _ _ _ _, _ => .lt
  | _, .function _ _ _ _ => .gt
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
    (cmp ⟨a, by simp only [Term.nesting] at ha; omega⟩
      ⟨b, by simp only [Term.nesting] at hb; omega⟩).then
      (cmp ⟨as, by simp only [Term.nesting] at ha; omega⟩
        ⟨bs, by simp only [Term.nesting] at hb; omega⟩)
  | .bitstring a ab _, .bitstring b bb _ =>
    List.compareLex Ord.compare (Bitstring.toBits a ab) (Bitstring.toBits b bb)
  | .bitstring _ _ _, _ => .gt
  | _, .bitstring _ _ _ => .lt

private theorem boundedStep_eq (exact : Bool) (n : Nat)
    (cmp exactCmp : Term → Term → Ordering) (a b : Term)
    (ha : Term.nesting a ≤ n) (hb : Term.nesting b ≤ n) :
    boundedStep exact n (fun a b => cmp a.val b.val) (fun a b => exactCmp a.val b.val)
      a b ha hb = compareStep exact cmp exactCmp a b := by
  cases a <;> cases b
  case function.function =>
    simp only [boundedStep, compareStep]
    rw [← lex_map exactCmp Subtype.val, boundedList_val, boundedList_val]
  case tuple.tuple =>
    simp only [boundedStep, compareStep]
    rw [← lex_map cmp Subtype.val, boundedList_val, boundedList_val]
  case map.map =>
    simp only [boundedStep, compareStep]
    rw [← compareMapViews_map exactCmp cmp Subtype.val, mapView_map, mapView_map,
      boundedEntries_val, boundedEntries_val]
  all_goals rfl

/-- Exact comparison without a step bound, to prove that enough steps decide it. -/
private def exactWF (a b : Term) : Ordering :=
  boundedStep true (max (Term.nesting a) (Term.nesting b))
    (fun x y => exactWF x.val y.val) (fun x y => exactWF x.val y.val)
    a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)
termination_by max (Term.nesting a) (Term.nesting b)
decreasing_by all_goals exact Nat.max_lt.mpr ⟨x.property, y.property⟩

private theorem exactWF_eq_step (a b : Term) :
    exactWF a b = compareStep true exactWF exactWF a b := by
  rw [exactWF]
  exact boundedStep_eq _ _ _ _ _ _ _ _

/-- Comparison without a step bound, to prove that enough steps decide it. -/
private def compareWF (a b : Term) : Ordering :=
  boundedStep false (max (Term.nesting a) (Term.nesting b))
    (fun x y => compareWF x.val y.val) (fun x y => exactWF x.val y.val)
    a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)
termination_by max (Term.nesting a) (Term.nesting b)
decreasing_by exact Nat.max_lt.mpr ⟨x.property, y.property⟩

private theorem compareWF_eq_step (a b : Term) :
    compareWF a b = compareStep false compareWF exactWF a b := by
  rw [compareWF]
  exact boundedStep_eq _ _ _ _ _ _ _ _

private theorem compareExact_eq_wf (n : Nat) (a b : Term)
    (h : max (Term.nesting a) (Term.nesting b) < n) : Term.compareExact n a b = exactWF a b := by
  induction n generalizing a b with
  | zero => omega
  | succ n ih =>
    rw [exactWF, Term.compareExact,
      ← boundedStep_eq true (max (Term.nesting a) (Term.nesting b)) (Term.compareExact n)
        (Term.compareExact n) a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
    congr 1 <;> funext x y <;>
      exact ih x.val y.val (by have := x.property; have := y.property; omega)

private theorem compare_eq_wf (n : Nat) (a b : Term)
    (h : max (Term.nesting a) (Term.nesting b) < n) : Term.compare n a b = compareWF a b := by
  induction n generalizing a b with
  | zero => omega
  | succ n ih =>
    rw [compareWF, Term.compare,
      ← boundedStep_eq false (max (Term.nesting a) (Term.nesting b)) (Term.compare n)
        (Term.compareExact n) a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
    congr 1 <;> funext x y
    · exact ih x.val y.val (by have := x.property; have := y.property; omega)
    · exact compareExact_eq_wf n x.val y.val (by have := x.property; have := y.property; omega)

end Lynx.Term.Compare

/-! ## Ordering laws -/

namespace Lynx.Term.Compare

/-- Erlang's type order, with integers and floats sharing the number rank. -/
private def rank : Term → Nat
  | .integer _ | .float _ => 0
  | .atom _ => 1
  | .reference _ => 2
  | .function _ _ _ _ => 3
  | .pid _ => 4
  | .tuple _ => 5
  | .map _ => 6
  | .nil => 7
  | .cons _ _ => 8
  | .bitstring _ _ _ => 9

/-- Terms of different ranks compare by rank alone. -/
private theorem compareStep_of_rank_ne {exact : Bool} {cmp exactCmp : Term → Term → Ordering}
    {a b : Term} (h : rank a ≠ rank b) :
    compareStep exact cmp exactCmp a b = Ord.compare (rank a) (rank b) := by
  cases a <;> cases b <;> first | exact absurd rfl h | rfl

private instance (exact : Bool) (cmp exactCmp : Term → Term → Ordering)
    [Std.TransCmp cmp] [Std.TransCmp exactCmp] :
    Std.TransCmp (compareStep exact cmp exactCmp) where
  eq_swap := by
    intro a b
    by_cases rab : rank a = rank b
    · cases a <;> cases b <;> simp only [rank, Nat.reduceEqDiff] at rab <;> cases exact <;>
        simp only [compareStep, Bool.false_eq_true, ite_false, ite_true, Ordering.swap_then,
          Ordering.swap_eq, Ordering.swap_lt, Ordering.swap_gt]
      all_goals first
        | exact Std.OrientedCmp.eq_swap
        | rfl
        | (congr 1 <;> exact Std.OrientedCmp.eq_swap)
        | (congr 1 <;> first
            | exact Std.OrientedCmp.eq_swap
            | (congr 1 <;> first
                | exact Std.OrientedCmp.eq_swap
                | (congr 1 <;> exact Std.OrientedCmp.eq_swap)))
    · rw [compareStep_of_rank_ne rab, compareStep_of_rank_ne (Ne.symm rab)]
      exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c ab bc
    by_cases rab : rank a = rank b
    · by_cases rbc : rank b = rank c
      · cases a <;> cases b <;> simp only [rank, Nat.reduceEqDiff] at rab <;>
          cases c <;> simp only [rank, Nat.reduceEqDiff] at rbc <;> cases exact <;>
          simp only [compareStep, Ordering.isLE_lt, Ordering.isLE_eq, Ordering.isLE_gt,
            Bool.false_eq_true, ite_false, ite_true] at ab bc ⊢
        all_goals try contradiction
        all_goals try trivial
        all_goals try exact Std.TransCmp.isLE_trans ab bc
        case function.function.function.false am an arity ac bm bn barity bcaps cm cn carity cc =>
          exact Std.TransCmp.isLE_trans
            (cmp := compareLex (compareOn stringCompare Prod.fst)
              (compareLex (compareOn stringCompare fun p : String × String × Nat × List Term => p.2.1)
                (compareLex (compareOn Ord.compare fun p : String × String × Nat × List Term => p.2.2.1)
                  (compareOn (List.compareLex exactCmp) fun p : String × String × Nat × List Term =>
                    p.2.2.2))))
            (a := (am, an, arity, ac.toList)) (b := (bm, bn, barity, bcaps.toList))
            (c := (cm, cn, carity, cc.toList)) ab bc
        case function.function.function.true am an arity ac bm bn barity bcaps cm cn carity cc =>
          exact Std.TransCmp.isLE_trans
            (cmp := compareLex (compareOn stringCompare Prod.fst)
              (compareLex (compareOn stringCompare fun p : String × String × Nat × List Term => p.2.1)
                (compareLex (compareOn Ord.compare fun p : String × String × Nat × List Term => p.2.2.1)
                  (compareOn (List.compareLex exactCmp) fun p : String × String × Nat × List Term =>
                    p.2.2.2))))
            (a := (am, an, arity, ac.toList)) (b := (bm, bn, barity, bcaps.toList))
            (c := (cm, cn, carity, cc.toList)) ab bc
        case tuple.tuple.tuple.false a b c =>
          exact Std.TransCmp.isLE_trans
            (cmp := compareLex (compareOn Ord.compare Array.size) (compareOn (List.compareLex cmp) Array.toList)) ab bc
        case tuple.tuple.tuple.true a b c =>
          exact Std.TransCmp.isLE_trans
            (cmp := compareLex (compareOn Ord.compare Array.size) (compareOn (List.compareLex cmp) Array.toList)) ab bc
        case cons.cons.cons.false ah ats bh bt ch ct =>
          exact Std.TransCmp.isLE_trans
            (cmp := compareLex (compareOn cmp Prod.fst) (compareOn cmp Prod.snd))
            (a := (ah,ats)) (b := (bh,bt)) (c := (ch,ct)) ab bc
        case cons.cons.cons.true ah ats bh bt ch ct =>
          exact Std.TransCmp.isLE_trans
            (cmp := compareLex (compareOn cmp Prod.fst) (compareOn cmp Prod.snd))
            (a := (ah,ats)) (b := (bh,bt)) (c := (ch,ct)) ab bc
      · rw [compareStep_of_rank_ne rbc, Nat.isLE_compare] at bc
        rw [compareStep_of_rank_ne (by omega), Nat.isLE_compare]
        omega
    · rw [compareStep_of_rank_ne rab, Nat.isLE_compare] at ab
      by_cases rbc : rank b = rank c
      · rw [compareStep_of_rank_ne (by omega), Nat.isLE_compare]
        omega
      · rw [compareStep_of_rank_ne rbc, Nat.isLE_compare] at bc
        rw [compareStep_of_rank_ne (by omega), Nat.isLE_compare]
        omega

end Lynx.Term.Compare

namespace Lynx.Term

/-- Exact comparison with any number of steps is a total order. -/
instance (fuel : Nat) : Std.TransCmp (compareExact fuel) := by
  induction fuel with
  | zero => exact { eq_swap := by intros; rfl, isLE_trans := by intros; rfl }
  | succ fuel ih =>
    letI := ih
    exact inferInstanceAs
      (Std.TransCmp (Compare.compareStep true (compareExact fuel) (compareExact fuel)))

/-- Comparison with any number of steps is a total order. -/
instance (fuel : Nat) : Std.TransCmp (compare fuel) := by
  induction fuel with
  | zero => exact { eq_swap := by intros; rfl, isLE_trans := by intros; rfl }
  | succ fuel ih =>
    letI := ih
    exact inferInstanceAs
      (Std.TransCmp (Compare.compareStep false (compare fuel) (compareExact fuel)))

theorem fuel_comm (a b : Term) : fuel a b = fuel b a := by
  simp only [fuel, Nat.max_comm]

/-- More steps than `Term.fuel` decide the same. -/
theorem compareExact_fuel {n : Nat} {a b : Term} (enough : fuel a b ≤ n) :
    compareExact n a b = compareExact (fuel a b) a b := by
  simp only [fuel] at enough ⊢
  rw [Compare.compareExact_eq_wf n a b (by omega), Compare.compareExact_eq_wf _ a b (by omega)]

/-- More steps than `Term.fuel` decide the same. -/
theorem compare_fuel {n : Nat} {a b : Term} (enough : fuel a b ≤ n) :
    compare n a b = compare (fuel a b) a b := by
  simp only [fuel] at enough ⊢
  rw [Compare.compare_eq_wf n a b (by omega), Compare.compare_eq_wf _ a b (by omega)]

/-- Exact comparison compares the children of two terms with the steps they need. -/
theorem compareExact_step (a b : Term) :
    compareExact (fuel a b) a b =
      Compare.compareStep true (fun x y => compareExact (fuel x y) x y)
        (fun x y => compareExact (fuel x y) x y) a b := by
  have children : Compare.exactWF = fun x y => compareExact (fuel x y) x y := by
    funext x y
    rw [Compare.compareExact_eq_wf _ x y (by simp [fuel])]
  rw [Compare.compareExact_eq_wf _ a b (by simp [fuel]), Compare.exactWF_eq_step, children]

/-- Comparison compares the children of two terms with the steps they need. -/
theorem compare_step (a b : Term) :
    compare (fuel a b) a b =
      Compare.compareStep false (fun x y => compare (fuel x y) x y)
        (fun x y => compareExact (fuel x y) x y) a b := by
  have exact : Compare.exactWF = fun x y => compareExact (fuel x y) x y := by
    funext x y
    rw [Compare.compareExact_eq_wf _ x y (by simp [fuel])]
  have numeric : Compare.compareWF = fun x y => compare (fuel x y) x y := by
    funext x y
    rw [Compare.compare_eq_wf _ x y (by simp [fuel])]
  rw [Compare.compare_eq_wf _ a b (by simp [fuel]), Compare.compareWF_eq_step, exact, numeric]

/-- Exact comparison with the steps each pair of terms needs is a total order. -/
private instance : Std.TransCmp fun a b => compareExact (fuel a b) a b where
  eq_swap := by
    intro a b
    show compareExact (fuel a b) a b = (compareExact (fuel b a) b a).swap
    rw [fuel_comm b a]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c ab bc
    show (compareExact (fuel a c) a c).isLE
    let n := max (max (fuel a b) (fuel b c)) (fuel a c)
    change (compareExact (fuel a b) a b).isLE at ab
    change (compareExact (fuel b c) b c).isLE at bc
    rw [← compareExact_fuel (n := n) (by omega)] at ab bc ⊢
    exact Std.TransCmp.isLE_trans ab bc

/-- Comparison with the steps each pair of terms needs is a total order. -/
private instance : Std.TransCmp fun a b => compare (fuel a b) a b where
  eq_swap := by
    intro a b
    show compare (fuel a b) a b = (compare (fuel b a) b a).swap
    rw [fuel_comm b a]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c ab bc
    show (compare (fuel a c) a c).isLE
    let n := max (max (fuel a b) (fuel b c)) (fuel a c)
    change (compare (fuel a b) a b).isLE at ab
    change (compare (fuel b c) b c).isLE at bc
    rw [← compare_fuel (n := n) (by omega)] at ab bc ⊢
    exact Std.TransCmp.isLE_trans ab bc



/-! ### Order laws with the steps each pair of terms needs -/

section

variable {a b c : Term}

theorem compare_eq_symm (equal : compare (fuel a b) a b = .eq) : compare (fuel b a) b a = .eq :=
  Std.OrientedCmp.eq_symm (cmp := fun a b => compare (fuel a b) a b) equal

theorem compare_gt_iff_lt : compare (fuel a b) a b = .gt ↔ compare (fuel b a) b a = .lt :=
  Std.OrientedCmp.gt_iff_lt (cmp := fun a b => compare (fuel a b) a b)

theorem compare_lt_of_gt (greater : compare (fuel a b) a b = .gt) : compare (fuel b a) b a = .lt :=
  Std.OrientedCmp.lt_of_gt (cmp := fun a b => compare (fuel a b) a b) greater

theorem compare_gt_of_lt (less : compare (fuel a b) a b = .lt) : compare (fuel b a) b a = .gt :=
  Std.OrientedCmp.gt_of_lt (cmp := fun a b => compare (fuel a b) a b) less

theorem compare_eq_trans (first : compare (fuel a b) a b = .eq) (second : compare (fuel b c) b c = .eq) :
    compare (fuel a c) a c = .eq :=
  Std.TransCmp.eq_trans (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_lt_trans (first : compare (fuel a b) a b = .lt) (second : compare (fuel b c) b c = .lt) :
    compare (fuel a c) a c = .lt :=
  Std.TransCmp.lt_trans (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_gt_trans (first : compare (fuel a b) a b = .gt) (second : compare (fuel b c) b c = .gt) :
    compare (fuel a c) a c = .gt :=
  Std.TransCmp.gt_trans (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_isLE_trans (first : (compare (fuel a b) a b).isLE) (second : (compare (fuel b c) b c).isLE) :
    (compare (fuel a c) a c).isLE :=
  Std.TransCmp.isLE_trans (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_lt_of_eq_of_lt (first : compare (fuel a b) a b = .eq) (second : compare (fuel b c) b c = .lt) :
    compare (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_eq_of_lt (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_lt_of_lt_of_eq (first : compare (fuel a b) a b = .lt) (second : compare (fuel b c) b c = .eq) :
    compare (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_lt_of_eq (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_lt_of_isLE_of_lt (first : (compare (fuel a b) a b).isLE) (second : compare (fuel b c) b c = .lt) :
    compare (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_isLE_of_lt (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_lt_of_lt_of_isLE (first : compare (fuel a b) a b = .lt) (second : (compare (fuel b c) b c).isLE) :
    compare (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_lt_of_isLE (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_gt_of_eq_of_gt (first : compare (fuel a b) a b = .eq) (second : compare (fuel b c) b c = .gt) :
    compare (fuel a c) a c = .gt :=
  Std.TransCmp.gt_of_eq_of_gt (cmp := fun a b => compare (fuel a b) a b) first second

theorem compare_congr_left (equal : compare (fuel a b) a b = .eq) :
    compare (fuel a c) a c = compare (fuel b c) b c :=
  Std.TransCmp.congr_left (cmp := fun a b => compare (fuel a b) a b) equal

theorem compareExact_eq_symm (equal : compareExact (fuel a b) a b = .eq) : compareExact (fuel b a) b a = .eq :=
  Std.OrientedCmp.eq_symm (cmp := fun a b => compareExact (fuel a b) a b) equal

theorem compareExact_gt_iff_lt : compareExact (fuel a b) a b = .gt ↔ compareExact (fuel b a) b a = .lt :=
  Std.OrientedCmp.gt_iff_lt (cmp := fun a b => compareExact (fuel a b) a b)

theorem compareExact_lt_of_gt (greater : compareExact (fuel a b) a b = .gt) : compareExact (fuel b a) b a = .lt :=
  Std.OrientedCmp.lt_of_gt (cmp := fun a b => compareExact (fuel a b) a b) greater

theorem compareExact_gt_of_lt (less : compareExact (fuel a b) a b = .lt) : compareExact (fuel b a) b a = .gt :=
  Std.OrientedCmp.gt_of_lt (cmp := fun a b => compareExact (fuel a b) a b) less

theorem compareExact_eq_trans (first : compareExact (fuel a b) a b = .eq) (second : compareExact (fuel b c) b c = .eq) :
    compareExact (fuel a c) a c = .eq :=
  Std.TransCmp.eq_trans (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_lt_trans (first : compareExact (fuel a b) a b = .lt) (second : compareExact (fuel b c) b c = .lt) :
    compareExact (fuel a c) a c = .lt :=
  Std.TransCmp.lt_trans (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_gt_trans (first : compareExact (fuel a b) a b = .gt) (second : compareExact (fuel b c) b c = .gt) :
    compareExact (fuel a c) a c = .gt :=
  Std.TransCmp.gt_trans (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_isLE_trans (first : (compareExact (fuel a b) a b).isLE) (second : (compareExact (fuel b c) b c).isLE) :
    (compareExact (fuel a c) a c).isLE :=
  Std.TransCmp.isLE_trans (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_lt_of_eq_of_lt (first : compareExact (fuel a b) a b = .eq) (second : compareExact (fuel b c) b c = .lt) :
    compareExact (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_eq_of_lt (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_lt_of_lt_of_eq (first : compareExact (fuel a b) a b = .lt) (second : compareExact (fuel b c) b c = .eq) :
    compareExact (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_lt_of_eq (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_lt_of_isLE_of_lt (first : (compareExact (fuel a b) a b).isLE) (second : compareExact (fuel b c) b c = .lt) :
    compareExact (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_isLE_of_lt (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_lt_of_lt_of_isLE (first : compareExact (fuel a b) a b = .lt) (second : (compareExact (fuel b c) b c).isLE) :
    compareExact (fuel a c) a c = .lt :=
  Std.TransCmp.lt_of_lt_of_isLE (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_gt_of_eq_of_gt (first : compareExact (fuel a b) a b = .eq) (second : compareExact (fuel b c) b c = .gt) :
    compareExact (fuel a c) a c = .gt :=
  Std.TransCmp.gt_of_eq_of_gt (cmp := fun a b => compareExact (fuel a b) a b) first second

theorem compareExact_congr_left (equal : compareExact (fuel a b) a b = .eq) :
    compareExact (fuel a c) a c = compareExact (fuel b c) b c :=
  Std.TransCmp.congr_left (cmp := fun a b => compareExact (fuel a b) a b) equal

end

@[simp] theorem compareExact_self (a : Term) : compareExact (fuel a a) a a = .eq :=
  Std.ReflCmp.compare_self (cmp := fun a b => compareExact (fuel a b) a b)

@[simp] theorem compare_self (a : Term) : compare (fuel a a) a a = .eq :=
  Std.ReflCmp.compare_self (cmp := fun a b => compare (fuel a b) a b)

theorem compareExact_swap (a b : Term) :
    compareExact (fuel a b) a b = (compareExact (fuel b a) b a).swap :=
  Std.OrientedCmp.eq_swap (cmp := fun a b => compareExact (fuel a b) a b)

theorem compare_swap (a b : Term) : compare (fuel a b) a b = (compare (fuel b a) b a).swap :=
  Std.OrientedCmp.eq_swap (cmp := fun a b => compare (fuel a b) a b)

end Lynx.Term

/-- Exact comparison with the steps each pair of terms needs. -/
local notation "exactOrder" => fun a b : Lynx.Term => Lynx.Term.compareExact (Lynx.Term.fuel a b) a b

/-- Comparison with the steps each pair of terms needs. -/
local notation "numericOrder" => fun a b : Lynx.Term => Lynx.Term.compare (Lynx.Term.fuel a b) a b

/-! ## Exact equality -/

namespace Lynx.Term

@[simp] theorem compareExact_integers (a b : Int) :
    compareExact (fuel (.integer a) (.integer b)) (.integer a) (.integer b) = Ord.compare a b := by
  rw [compareExact_step]
  rfl

@[simp] theorem compareExact_atoms (a b : String) :
    compareExact (fuel (.atom a) (.atom b)) (.atom a) (.atom b) = Ord.compare a b := by
  rw [compareExact_step]
  exact Compare.stringCompare_eq a b

theorem compare_atoms (a b : String) :
    compare (fuel (.atom a) (.atom b)) (.atom a) (.atom b) = Ord.compare a b := by
  rw [compare_step]
  exact Compare.stringCompare_eq a b

@[simp] theorem compareExact_reference (a b : List Nat) :
    compareExact (fuel (.reference a) (.reference b)) (.reference a) (.reference b) = Ord.compare a b := by
  rw [compareExact_step]
  rfl

@[simp] theorem compareExact_pid (a b : PID) :
    compareExact (fuel (.pid a) (.pid b)) (.pid a) (.pid b) = Ord.compare a b := by
  rw [compareExact_step]
  rfl

@[simp] theorem compareExact_eq_atom (a : Term) (name : String) :
    compareExact (fuel a (.atom name)) a (.atom name) = .eq ↔ a = .atom name := by
  cases a <;> rw [compareExact_step] <;> simp [Compare.compareStep]

/-- Only bitstrings are exactly equal to a bitstring. -/
theorem bitstring_compareExact_eq (bytes : ByteArray) (lastBits : Fin 8)
    (valid : Bitstring.Valid bytes lastBits) (a : Term)
    (equal : compareExact (fuel (.bitstring bytes lastBits valid) a) (.bitstring bytes lastBits valid) a = .eq) :
    ∃ other otherBits otherValid, a = .bitstring other otherBits otherValid := by
  cases a <;> rw [compareExact_step] at equal <;> simp [Compare.compareStep] at equal
  exact ⟨_, _, _, rfl⟩

/-- Binaries are exactly equal when they have the same bytes. -/
theorem binary_compareExact_eq (a b : ByteArray) :
    compareExact (fuel (.bitstring a 0 (Bitstring.valid_aligned a)) (.bitstring b 0 (Bitstring.valid_aligned b))) (.bitstring a 0 (Bitstring.valid_aligned a)) (.bitstring b 0 (Bitstring.valid_aligned b)) =
      .eq ↔ a = b := by
  rw [compareExact_step]
  simp only [Compare.compareStep]
  constructor
  · intro equal
    have bits := Std.LawfulEqCmp.eq_of_compare equal
    rw [← Bitstring.pack_toBits_aligned a, ← Bitstring.pack_toBits_aligned b, bits]
  · rintro rfl
    exact Std.ReflCmp.compare_self

private theorem mapViewInsert_ne_nil (cmp : α → α → Ordering) (e : α × α) (xs : List (α × α)) :
    Compare.mapViewInsert cmp e xs ≠ [] := by
  cases xs with
  | nil => simp [Compare.mapViewInsert]
  | cons p xs =>
    simp only [Compare.mapViewInsert]
    split <;> simp

/-- Only maps without bindings are exactly equal to the empty map. -/
theorem map_compareExact_empty (entries : List (Term × Term))
    (equal : compareExact (fuel (.map entries) (.map [])) (.map entries) (.map []) = .eq) : entries = [] := by
  cases entries with
  | nil => rfl
  | cons e es =>
    exfalso
    rw [compareExact_step] at equal
    simp only [Compare.compareStep, Compare.mapView] at equal
    have nonempty := mapViewInsert_ne_nil exactOrder e (Compare.mapView exactOrder es)
    obtain ⟨p, ps, view⟩ := List.exists_cons_of_ne_nil nonempty
    rw [view] at equal
    simp [Compare.compareMapViews, compareLex, Compare.compareOn] at equal

/-- Only maps without bindings are equal to the empty map. -/
@[simp] theorem compare_map_empty (entries : List (Term × Term)) :
    compare (fuel (.map entries) (.map [])) (.map entries) (.map []) = .eq ↔ entries = [] := by
  constructor
  · intro equal
    cases entries with
    | nil => rfl
    | cons e es =>
      exfalso
      rw [compare_step] at equal
      simp only [Compare.compareStep, Compare.mapView] at equal
      have nonempty := mapViewInsert_ne_nil exactOrder e (Compare.mapView exactOrder es)
      obtain ⟨p, ps, view⟩ := List.exists_cons_of_ne_nil nonempty
      rw [view] at equal
      simp [Compare.compareMapViews, compareLex, Compare.compareOn] at equal
  · rintro rfl
    exact compare_self _

@[simp] theorem compareExact_eq_nil (a : Term) : compareExact (fuel a .nil) a .nil = .eq ↔ a = .nil := by
  cases a <;> rw [compareExact_step] <;> simp [Compare.compareStep]

/-- Only nonempty lists are exactly equal to a nonempty list. -/
theorem cons_compareExact_eq (head tail a : Term) (equal : compareExact (fuel (.cons head tail) a) (.cons head tail) a = .eq) :
    ∃ otherHead otherTail, a = .cons otherHead otherTail := by
  cases a <;> rw [compareExact_step] at equal <;> simp [Compare.compareStep] at equal
  exact ⟨_, _, rfl⟩

@[simp] theorem compareExact_eq_integer (a : Term) (n : Int) :
    compareExact (fuel a (.integer n)) a (.integer n) = .eq ↔ a = .integer n := by
  cases a <;> rw [compareExact_step] <;> simp [Compare.compareStep]

@[simp] theorem integer_compareExact_eq (n : Int) (a : Term) :
    compareExact (fuel (.integer n) a) (.integer n) a = .eq ↔ a = .integer n := by
  rw [Std.OrientedCmp.eq_swap (cmp := exactOrder), Ordering.swap_eq_eq]
  exact compareExact_eq_integer a n

@[simp] theorem compareExact_eq_reference (a : Term) (id : List Nat) :
    compareExact (fuel a (.reference id)) a (.reference id) = .eq ↔ a = .reference id := by
  cases a <;> rw [compareExact_step] <;> simp [Compare.compareStep]

@[simp] theorem reference_compareExact_eq (id : List Nat) (a : Term) :
    compareExact (fuel (.reference id) a) (.reference id) a = .eq ↔ a = .reference id := by
  rw [Std.OrientedCmp.eq_swap (cmp := exactOrder), Ordering.swap_eq_eq]
  exact compareExact_eq_reference a id

@[simp] theorem compareExact_eq_float (a : Term) (n : FiniteFloat) :
    compareExact (fuel a (.float n)) a (.float n) = .eq ↔ a = .float n := by
  cases a <;> rw [compareExact_step] <;> simp [Compare.compareStep]
@[simp] theorem float_compareExact_eq (n : FiniteFloat) (a : Term) :
    compareExact (fuel (.float n) a) (.float n) a = .eq ↔ a = .float n := by
  rw [Std.OrientedCmp.eq_swap (cmp := exactOrder), Ordering.swap_eq_eq]
  exact compareExact_eq_float a n

@[simp] theorem compareExact_eq_closed_function (a : Term) (module name : String) (arity : Nat) :
    compareExact (fuel a (.function module name arity #[])) a (.function module name arity #[]) = .eq ↔ a = .function module name arity #[] := by
  cases a <;> rw [compareExact_step] <;> simp [Compare.compareStep]
  rintro rfl rfl rfl
  rename_i captures
  rcases captures with ⟨_ | _⟩ <;> simp [List.compareLex]

end Lynx.Term

/-! ## Numeric equality -/

namespace Lynx.Term

@[simp] theorem compare_reference (a b : List Nat) :
    compare (fuel (.reference a) (.reference b)) (.reference a) (.reference b) = Ord.compare a b := by
  rw [compare_step]
  rfl

@[simp] theorem compare_pid (a b : PID) :
    compare (fuel (.pid a) (.pid b)) (.pid a) (.pid b) = Ord.compare a b := by
  rw [compare_step]
  rfl

/-- Binaries compare (fuel equal when) equal when they have the same bytes. -/
theorem binary_compare_eq (a b : ByteArray) :
    compare (fuel (.bitstring a 0 (Bitstring.valid_aligned a)) (.bitstring b 0 (Bitstring.valid_aligned b))) (.bitstring a 0 (Bitstring.valid_aligned a)) (.bitstring b 0 (Bitstring.valid_aligned b)) =
      .eq ↔ a = b := by
  rw [compare_step]
  simp only [Compare.compareStep]
  constructor
  · intro equal
    have bits := Std.LawfulEqCmp.eq_of_compare equal
    rw [← Bitstring.pack_toBits_aligned a, ← Bitstring.pack_toBits_aligned b, bits]
  · rintro rfl
    exact Std.ReflCmp.compare_self

@[simp] theorem compare_eq_nil (a : Term) : compare (fuel a .nil) a .nil = .eq ↔ a = .nil := by
  cases a <;> rw [compare_step] <;> simp [Compare.compareStep]
@[simp] theorem nil_compare_eq (a : Term) : compare (fuel .nil a) .nil a = .eq ↔ a = .nil := by
  rw [Std.OrientedCmp.eq_swap (cmp := numericOrder), Ordering.swap_eq_eq]
  exact compare_eq_nil a

/-- Only the same atom is equal to an atom. -/
@[simp] theorem compare_eq_atom (a : Term) (name : String) :
    compare (fuel a (.atom name)) a (.atom name) = .eq ↔ a = .atom name := by
  cases a <;> rw [compare_step] <;> simp [Compare.compareStep]

@[simp] theorem compare_integers (a b : Int) :
    compare (fuel (.integer a) (.integer b)) (.integer a) (.integer b) = Ord.compare a b := by
  rw [compare_step]
  by_cases hab : a < b <;> by_cases hba : b < a <;> by_cases eq : a = b <;>
    simp [Compare.compareStep, Compare.ratCompare, compareOfLessAndEq,
      Int.compare_eq_ite_lt, Rat.intCast_lt_intCast, hab, hba, eq] <;> omega

/-- Float ordering agrees with the exact rational value of each encoding. -/
theorem compare_floats (a b : FiniteFloat) :
    compare (fuel (.float a) (.float b)) (.float a) (.float b) = compareOfLessAndEq a.toRat b.toRat := by
  rw [compare_step]
  rfl

@[simp] theorem integer_compare_integer_eq (a b : Int) :
    compare (fuel (.integer a) (.integer b)) (.integer a) (.integer b) = .eq ↔ a = b := by
  rw [compare_step]
  simp [Compare.compareStep]
@[simp] theorem integer_compare_float_eq (integer : Int) (float : FiniteFloat) :
    compare (fuel (.integer integer) (.float float)) (.integer integer) (.float float) = .eq ↔ integer = float.toRat := by
  rw [compare_step]
  simp [Compare.compareStep]
@[simp] theorem float_compare_integer_eq (float : FiniteFloat) (integer : Int) :
    compare (fuel (.float float) (.integer integer)) (.float float) (.integer integer) = .eq ↔ float.toRat = integer := by
  rw [compare_step]
  simp [Compare.compareStep]
@[simp] theorem float_compare_float_eq (a b : FiniteFloat) :
    compare (fuel (.float a) (.float b)) (.float a) (.float b) = .eq ↔ a.toRat = b.toRat := by
  rw [compare_step]
  simp [Compare.compareStep]

end Lynx.Term

namespace Lynx

/-- Executable semantic equality. Lean `=` still compares representations. -/
instance : BEq Term := ⟨fun a b => decide (Term.compare (Term.fuel a b) a b = .eq)⟩

@[simp] theorem Term.beq_iff_compare_eq (a b : Term) :
    (a == b) = true ↔ Term.compare (Term.fuel a b) a b = .eq := by
  change decide (Term.compare (Term.fuel a b) a b = .eq) = true ↔ _
  simp

instance : EquivBEq Term where
  rfl := by intro a; exact (Term.beq_iff_compare_eq a a).mpr (Term.compare_self a)
  symm := by
    intro a b h
    exact (Term.beq_iff_compare_eq b a).mpr
      (Std.OrientedCmp.eq_symm (cmp := numericOrder) ((Term.beq_iff_compare_eq a b).mp h))
  trans := by
    intro a b c h h'
    exact (Term.beq_iff_compare_eq a c).mpr
      (Std.TransCmp.eq_trans (cmp := numericOrder) ((Term.beq_iff_compare_eq a b).mp h)
        ((Term.beq_iff_compare_eq b c).mp h'))

end Lynx

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

/-- The visible bindings of a map are among its bindings. -/
theorem mem_mapView {xs : List (α × α)} {p : α × α} (h : p ∈ mapView cmp xs) : p ∈ xs := by
  induction xs with
  | nil => simp [mapView] at h
  | cons e xs ih =>
    rcases mem_mapViewInsert cmp h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

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

/-- Exact comparison keeps integer and float representations distinct. -/
@[simp] theorem compareExact_integer_float (integer : Int) (float : FiniteFloat) :
    compareExact (fuel (.integer integer) (.float float)) (.integer integer) (.float float) = .lt := by
  rw [compareExact_step]
  rfl

@[simp] theorem compareExact_float_integer (float : FiniteFloat) (integer : Int) :
    compareExact (fuel (.float float) (.integer integer)) (.float float) (.integer integer) = .gt := by
  rw [compareExact_step]
  rfl

/-- Tuples compareExact (fuel arity before) arity before their elements. -/
theorem compareExact_tuple (a b : Array Term) :
    compareExact (fuel (.tuple a) (.tuple b)) (.tuple a) (.tuple b) =
      (Ord.compare a.size b.size).then (List.compareLex exactOrder a.toList b.toList) := by
  rw [compareExact_step]
  rfl

/-- Every number precedes every map under ordinary comparison. -/
theorem compare_integer_map (n : Int) (entries : List (Term × Term)) :
    compare (fuel (.integer n) (.map entries)) (.integer n) (.map entries) = .lt := by
  rw [compare_step]
  rfl

/-- Tuples compare (fuel arity before) arity before their elements. -/
theorem compare_tuple (a b : Array Term) :
    compare (fuel (.tuple a) (.tuple b)) (.tuple a) (.tuple b) =
      (Ord.compare a.size b.size).then (List.compareLex numericOrder a.toList b.toList) := by
  rw [compare_step]
  rfl

/-- Lists compareExact (fuel their heads) their heads before their tails. -/
theorem compareExact_cons (a as b bs : Term) :
    compareExact (fuel (.cons a as) (.cons b bs)) (.cons a as) (.cons b bs) = (compareExact (fuel a b) a b).then (compareExact (fuel as bs) as bs) := by
  rw [compareExact_step]
  rfl

/-- Lists compare (fuel their heads) their heads before their tails. -/
theorem compare_cons (a as b bs : Term) :
    compare (fuel (.cons a as) (.cons b bs)) (.cons a as) (.cons b bs) = (compare (fuel a b) a b).then (compare (fuel as bs) as bs) := by
  rw [compare_step]
  rfl

/-- A singleton map is larger than the empty map, regardless of its binding. -/
theorem compare_singleton_map_empty (k v : Term) :
    compare (fuel (.map [(k,v)]) (.map [])) (.map [(k,v)]) (.map []) = .gt := by
  rw [compare_step]
  rfl

/-- Singleton maps compare (fuel exact keys) exact keys before ordinarily compared values. -/
theorem compare_singleton_map (k v l w : Term) :
    compare (fuel (.map [(k,v)]) (.map [(l,w)])) (.map [(k,v)]) (.map [(l,w)]) =
      (compareExact (fuel k l) k l).then (compare (fuel v w) v w) := by
  rw [compare_step]
  simp [Compare.compareStep, Compare.mapView, Compare.mapViewInsert, Compare.compareMapViews,
    compareLex, Compare.compareOn, List.compareLex_cons_cons, List.compareLex_nil_nil]

/-- Matching first-binding lookups suffice for semantic map equality. -/
theorem map_compare_eq_of_lookup (a b : List (Term × Term))
    (h : ∀ q, Option.Rel (fun a b => compare (fuel a b) a b = .eq)
      ((a.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd)
      ((b.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd)) :
    compare (fuel (.map a) (.map b)) (.map a) (.map b) = .eq := by
  rw [compare_step]
  apply Compare.compareMapViews_eq_of_lookup (cmp := exactOrder) numericOrder _ _
    (Compare.mapView_sorted _ _) (Compare.mapView_sorted _ _)
  intro q
  simp only [Compare.mapViewLookup_view]
  exact h q

/-- Matching first-binding lookups, up to exact equality of values, suffice for
exact map equality. -/
theorem map_compareExact_eq_of_lookup (a b : List (Term × Term))
    (h : ∀ q, Option.Rel (fun a b => compareExact (fuel a b) a b = .eq)
      ((a.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd)
      ((b.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd)) :
    compareExact (fuel (.map a) (.map b)) (.map a) (.map b) = .eq := by
  rw [compareExact_step]
  apply Compare.compareMapViews_eq_of_lookup (cmp := exactOrder) exactOrder _ _
    (Compare.mapView_sorted _ _) (Compare.mapView_sorted _ _)
  intro q
  simp only [Compare.mapViewLookup_view]
  exact h q

private theorem mapViewLookup_rel (cmp : Term → Term → Ordering) {xs ys : List (Term × Term)}
    (keys : List.compareLex exactOrder (xs.map Prod.fst) (ys.map Prod.fst) = .eq)
    (values : List.compareLex cmp (xs.map Prod.snd) (ys.map Prod.snd) = .eq) (q : Term) :
    Option.Rel (fun a b => cmp a b = .eq) (Compare.mapViewLookup exactOrder xs q)
      (Compare.mapViewLookup exactOrder ys q) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact Option.Rel.none
    | cons y ys => simp [List.compareLex_nil_cons] at keys
  | cons x xs ih =>
    cases ys with
    | nil => simp [List.compareLex_cons_nil] at keys
    | cons y ys =>
      simp only [List.map_cons, List.compareLex_cons_cons, Ordering.then_eq_eq] at keys values
      simp only [Compare.mapViewLookup_cons]
      have same : compareExact (fuel q x.1) q x.1 = .eq ↔ compareExact (fuel q y.1) q y.1 = .eq :=
        ⟨fun h => Std.TransCmp.eq_trans (cmp := exactOrder) h keys.1,
          fun h => Std.TransCmp.eq_trans (cmp := exactOrder) h
            (Std.OrientedCmp.eq_symm (cmp := exactOrder) keys.1)⟩
      by_cases hit : compareExact (fuel q x.1) q x.1 = .eq
      · simp only [hit, ite_true, same.mp hit]
        exact Option.Rel.some values.1
      · simp only [hit, (not_congr same).mp hit]
        exact ih keys.2 values.2

/-- Exactly equal maps have exactly equal first-binding lookups. -/
theorem lookup_of_map_compareExact_eq (a b : List (Term × Term))
    (equal : compareExact (fuel (.map a) (.map b)) (.map a) (.map b) = .eq) (q : Term) :
    Option.Rel (fun x y => compareExact (fuel x y) x y = .eq)
      ((a.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd)
      ((b.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd) := by
  rw [compareExact_step] at equal
  simp only [Compare.compareStep, Compare.compareMapViews, compareLex, Compare.compareOn,
    Ordering.then_eq_eq] at equal
  have rel := mapViewLookup_rel exactOrder equal.2.1 equal.2.2 q
  simp only [Compare.mapViewLookup_view] at rel
  exact rel

/-- Semantically equal maps bind exactly equal keys to semantically equal values. -/
theorem lookup_of_map_compare_eq (a b : List (Term × Term))
    (equal : compare (fuel (.map a) (.map b)) (.map a) (.map b) = .eq) (q : Term) :
    Option.Rel (fun x y => compare (fuel x y) x y = .eq)
      ((a.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd)
      ((b.find? fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)).map Prod.snd) := by
  rw [compare_step] at equal
  simp only [Compare.compareStep, Compare.compareMapViews, compareLex, Compare.compareOn,
    Ordering.then_eq_eq] at equal
  have rel := mapViewLookup_rel numericOrder equal.2.1 equal.2.2 q
  simp only [Compare.mapViewLookup_view] at rel
  exact rel

/-- First-binding lookup of a key in a map's entries. -/
@[expose] def mapLookup (entries : List (Term × Term)) (key : Term) : Option Term :=
  (entries.find? fun entry => decide (compareExact (fuel key entry.1) key entry.1 = .eq)).map Prod.snd

/-- The visible bindings of a map, each key once, in an unspecified order.
Erlang does not specify map iteration order, so proofs may rely only on the
distinct keys, lookups, and bindings below. Execution enumerates the keys in
ascending order. -/
opaque mapEnumeration (entries : List (Term × Term)) :
    { enumerated : List (Term × Term) //
      enumerated.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq) ∧
      (∀ key, mapLookup enumerated key = mapLookup entries key) ∧
      ∀ entry ∈ enumerated, entry ∈ entries } :=
  ⟨Compare.mapView exactOrder entries,
    (Compare.mapView_sorted exactOrder entries).imp fun lt => by simp [lt],
    Compare.mapViewLookup_view exactOrder entries,
    fun _ => Compare.mem_mapView exactOrder⟩

/-- The visible bindings of a map, in an unspecified order. -/
def mapEntries (entries : List (Term × Term)) : List (Term × Term) :=
  (mapEnumeration entries).val

/-- Enumeration keeps the first binding of each key. -/
@[simp] theorem mapLookup_mapEntries (entries : List (Term × Term)) (key : Term) :
    mapLookup (mapEntries entries) key = mapLookup entries key :=
  (mapEnumeration entries).property.2.1 key

/-- Enumerated keys are distinct. -/
theorem mapEntries_distinct (entries : List (Term × Term)) :
    (mapEntries entries).Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq) :=
  (mapEnumeration entries).property.1

/-- Bindings with distinct keys are found by their own key. -/
private theorem mapLookup_of_mem {entries : List (Term × Term)} {entry : Term × Term}
    (distinct : entries.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq)) (member : entry ∈ entries) :
    mapLookup entries entry.1 = some entry.2 := by
  induction entries with
  | nil => simp at member
  | cons r rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [mapLookup]
    · have apart := (List.pairwise_cons.mp distinct).1 entry member
      have miss : compareExact (fuel entry.1 r.1) entry.1 r.1 ≠ .eq := fun same => apart (Std.OrientedCmp.eq_symm (cmp := exactOrder) same)
      have := ih (List.pairwise_cons.mp distinct).2 member
      simp only [mapLookup, List.find?_cons, miss, decide_false] at this ⊢
      exact this

/-- Enumerated bindings are found by their own key. -/
theorem mapLookup_of_mem_mapEntries {entries : List (Term × Term)} {entry : Term × Term}
    (member : entry ∈ mapEntries entries) : mapLookup entries entry.1 = some entry.2 := by
  rw [← mapLookup_mapEntries]
  exact mapLookup_of_mem (mapEntries_distinct entries) member

/-- Enumerated bindings are bindings of the map. -/
theorem mem_of_mem_mapEntries {entries : List (Term × Term)} {entry : Term × Term}
    (member : entry ∈ mapEntries entries) : entry ∈ entries :=
  (mapEnumeration entries).property.2.2 entry member

/-- A single binding enumerates as itself. -/
@[simp] theorem mapEntries_singleton (key value : Term) :
    mapEntries [(key, value)] = [(key, value)] := by
  have found := mapLookup_mapEntries [(key, value)] key
  have only : ∀ entry ∈ mapEntries [(key, value)], entry = (key, value) := fun entry member => by
    simpa using mem_of_mem_mapEntries member
  have distinct := mapEntries_distinct [(key, value)]
  match enumerated : mapEntries [(key, value)], only, distinct with
  | [], _, _ => simp [enumerated, mapLookup] at found
  | [entry], only, _ => rw [only entry (by simp)]
  | first :: second :: rest, only, distinct =>
    have first_eq := only first (by simp)
    have second_eq := only second (by simp)
    simp [first_eq, second_eq] at distinct

/-- The empty map enumerates no bindings. -/
@[simp] theorem mapEntries_nil : mapEntries [] = [] := by
  cases enumerated : mapEntries [] with
  | nil => rfl
  | cons entry rest =>
    have found := mapLookup_mapEntries [] entry.1
    simp [enumerated, mapLookup] at found

/-- Whether no two keys of a map's entries are exactly equal. -/
@[expose] def keysDistinct : List (Term × Term) → Bool
  | [] => .true
  | entry :: rest => rest.all (fun other => compareExact (fuel entry.1 other.1) entry.1 other.1 != .eq) && keysDistinct rest

/-- The lists inserting an element at each position of a list. -/
@[expose] def insertions (element : α) : List α → List (List α)
  | [] => [[element]]
  | first :: rest => (element :: first :: rest) :: (insertions element rest).map (first :: ·)

/-- Every order of a list. -/
@[expose] def orders : List α → List (List α)
  | [] => [[]]
  | first :: rest => (orders rest).flatMap (insertions first)

/-- A map has a key when one of its keys is exactly equal to it. -/
theorem mapLookup_isSome (entries : List (Term × Term)) (key : Term) :
    (mapLookup entries key).isSome ↔ ∃ entry ∈ entries, compareExact (fuel key entry.1) key entry.1 = .eq := by
  simp [mapLookup, List.find?_isSome]

/-- Exactly equal keys look up the same binding. -/
theorem mapLookup_congr {a b : Term} (equal : compareExact (fuel a b) a b = .eq) (entries : List (Term × Term)) :
    mapLookup entries a = mapLookup entries b := by
  have symm := Std.OrientedCmp.eq_symm (cmp := exactOrder) equal
  have same : (fun entry : Term × Term => decide (compareExact (fuel a entry.1) a entry.1 = .eq)) =
      fun entry => decide (compareExact (fuel b entry.1) b entry.1 = .eq) := by
    funext entry
    simp only [decide_eq_decide]
    exact ⟨fun h => Std.TransCmp.eq_trans (cmp := exactOrder) symm h, fun h => Std.TransCmp.eq_trans (cmp := exactOrder) equal h⟩
  simp only [mapLookup, same]

/-- Removing a key's bindings leaves the bindings of other keys. -/
theorem mapLookup_filter (entries : List (Term × Term)) (key query : Term) :
    mapLookup (entries.filter fun entry => compareExact (fuel key entry.1) key entry.1 != .eq) query =
      if compareExact (fuel query key) query key = .eq then none else mapLookup entries query := by
  induction entries with
  | nil => simp [mapLookup]
  | cons entry rest ih =>
    by_cases same : compareExact (fuel query key) query key = .eq
    · simp only [same, ite_true] at ih ⊢
      by_cases hit : compareExact (fuel key entry.1) key entry.1 = .eq
      · simp [hit, ih]
      · have miss : compareExact (fuel query entry.1) query entry.1 ≠ .eq := fun h =>
          hit (Std.TransCmp.eq_trans (cmp := exactOrder) (Std.OrientedCmp.eq_symm (cmp := exactOrder) same) h)
        simp [hit, mapLookup, miss] at ih ⊢
        exact ih
    · simp only [same, ite_false] at ih ⊢
      by_cases hit : compareExact (fuel key entry.1) key entry.1 = .eq
      · have miss : compareExact (fuel query entry.1) query entry.1 ≠ .eq := fun h =>
          same (Std.TransCmp.eq_trans (cmp := exactOrder) h (Std.OrientedCmp.eq_symm (cmp := exactOrder) hit))
        simp [hit, mapLookup, miss] at ih ⊢
        exact ih
      · by_cases found : compareExact (fuel query entry.1) query entry.1 = .eq
        · simp [hit, mapLookup, found]
        · simp [hit, mapLookup, found] at ih ⊢
          exact ih

/-- Whether a term is exactly equal to one of the candidates, as a Boolean atom.
Guards test membership in sets of literals as chains of `=:=` comparisons. -/
@[expose] def isMember (value : Term) : List Term → Term
  | [] => .atom "false"
  | candidate :: rest =>
    if compareExact (fuel value candidate) value candidate = .eq then .atom "true" else isMember value rest

@[simp] theorem isMember_nil (value : Term) : isMember value [] = .atom "false" := rfl

@[simp] theorem isMember_cons (value candidate : Term) (rest : List Term) :
    isMember value (candidate :: rest) =
      if compareExact (fuel value candidate) value candidate = .eq then .atom "true" else isMember value rest := rfl

end Lynx.Term

/-! ## Exact and ordinary equality -/

namespace Lynx.Term

/-- A lexicographic comparison that finds every pair equal still does so with a
comparator that equates at least as much. -/
private theorem compareLex_eq_mono {α : Type} {f g : α → α → Ordering} :
    ∀ {xs ys : List α}, (∀ x ∈ xs, ∀ y ∈ ys, f x y = .eq → g x y = .eq) →
      List.compareLex f xs ys = .eq → List.compareLex g xs ys = .eq
  | [], [], _, _ => List.compareLex_nil_nil
  | [], _ :: _, _, h => by simp [List.compareLex_nil_cons] at h
  | _ :: _, [], _, h => by simp [List.compareLex_cons_nil] at h
  | x :: xs, y :: ys, step, h => by
    rw [List.compareLex_cons_cons, Ordering.then_eq_eq] at h ⊢
    exact ⟨step x List.mem_cons_self y List.mem_cons_self h.1,
      compareLex_eq_mono (fun a ha b hb => step a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) h.2⟩

/-- Exactly equal terms are equal under ordinary comparison. -/
theorem compare_eq_of_compareExact_eq (a b : Term) (h : compareExact (fuel a b) a b = .eq) : compare (fuel a b) a b = .eq := by
  rw [compareExact_step] at h
  rw [compare_step]
  cases a <;> cases b
  all_goals try simp only [Compare.compareStep, ite_true, Bool.false_eq_true, ite_false, reduceCtorEq] at h ⊢
  all_goals first | exact h | skip
  case integer.integer x y =>
    have : x = y := by simpa using h
    subst this
    simp
  case float.float x y =>
    have : x = y := by simpa using h
    subst this
    simp
  case tuple.tuple xs ys =>
    simp only [Ordering.then_eq_eq] at h ⊢
    refine ⟨h.1, compareLex_eq_mono (fun x hx y hy e => ?_) h.2⟩
    have := Array.sizeOf_lt_of_mem (by simpa using hx : x ∈ xs)
    have := Array.sizeOf_lt_of_mem (by simpa using hy : y ∈ ys)
    exact compare_eq_of_compareExact_eq x y e
  case map.map xs ys =>
    simp only [Compare.compareMapViews, compareLex, Compare.compareOn, Ordering.then_eq_eq] at h ⊢
    refine ⟨h.1, h.2.1, compareLex_eq_mono (fun x hx y hy e => ?_) h.2.2⟩
    obtain ⟨⟨kx, vx⟩, mx, rfl⟩ := List.mem_map.mp hx
    obtain ⟨⟨ky, vy⟩, my, rfl⟩ := List.mem_map.mp hy
    have := List.sizeOf_lt_of_mem (Compare.mem_mapView exactOrder mx)
    have := List.sizeOf_lt_of_mem (Compare.mem_mapView exactOrder my)
    simp only [Prod.mk.sizeOf_spec] at *
    exact compare_eq_of_compareExact_eq vx vy e
  case cons.cons x xs y ys =>
    simp only [Ordering.then_eq_eq] at h ⊢
    exact ⟨compare_eq_of_compareExact_eq x y h.1, compare_eq_of_compareExact_eq xs ys h.2⟩
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals
    subst_vars
    simp only [Term.tuple.sizeOf_spec, Term.map.sizeOf_spec, Term.cons.sizeOf_spec,
      Prod.mk.sizeOf_spec] at *
    omega

end Lynx.Term

namespace Lynx

/-! ## Identical terms

Erlang's comparison equates `1` and `1.0`, and maps with shadowed bindings.
`Term.identical` compares the representations instead, field by field, so that
evaluation in the kernel can decide it, as checks of concurrent steps do. -/

mutual
/-- Whether two terms are the same term. -/
@[expose] def Term.identical : Term → Term → Bool
  | .integer first, .integer second => first == second
  | .float first, .float second =>
      first.negative == second.negative && first.exponent.val == second.exponent.val &&
        first.fraction.val == second.fraction.val
  | .atom first, .atom second => first == second
  | .reference first, .reference second => first == second
  | .function module name arity captures, .function module' name' arity' captures' =>
      module == module' && name == name' && arity == arity' &&
        Term.identicalList captures.toList captures'.toList
  | .pid first, .pid second => first == second
  | .tuple first, .tuple second => Term.identicalList first.toList second.toList
  | .map first, .map second => Term.identicalEntries first second
  | .nil, .nil => true
  | .cons head tail, .cons head' tail' => Term.identical head head' && Term.identical tail tail'
  | .bitstring bytes lastBits _, .bitstring bytes' lastBits' _ =>
      bytes.data == bytes'.data && lastBits == lastBits'
  | _, _ => false
termination_by structural first => first

/-- Whether two lists hold the same terms. -/
@[expose] def Term.identicalList : List Term → List Term → Bool
  | [], [] => true
  | first :: rest, second :: rest' => Term.identical first second && Term.identicalList rest rest'
  | _, _ => false
termination_by structural first => first

/-- Whether two lists hold the same pairs of terms. -/
@[expose] def Term.identicalEntries : List (Term × Term) → List (Term × Term) → Bool
  | [], [] => true
  | (key, value) :: rest, (key', value') :: rest' =>
      Term.identical key key' && Term.identical value value' && Term.identicalEntries rest rest'
  | _, _ => false
termination_by structural first => first
end

mutual
/-- Identical terms are equal. -/
theorem Term.eq_of_identical : ∀ {first second : Term},
    Term.identical first second = true → first = second
  | .function module name arity ⟨captures⟩, second, same => by
    cases second <;> simp only [Term.identical, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, same⟩ := same
    rw [Term.eq_of_identicalList same]
  | .tuple ⟨items⟩, second, same => by
    cases second <;> simp only [Term.identical, Bool.false_eq_true] at same
    rw [Term.eq_of_identicalList same]
  | .map entries, second, same => by
    cases second <;> simp only [Term.identical, Bool.false_eq_true] at same
    rw [Term.eq_of_identicalEntries same]
  | .cons head tail, second, same => by
    cases second <;> simp only [Term.identical, Bool.and_eq_true, Bool.false_eq_true] at same
    rw [Term.eq_of_identical same.1, Term.eq_of_identical same.2]
  | .bitstring ⟨bytes⟩ _ _, second, same => by
    cases second <;> simp only [Term.identical, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    obtain ⟨rfl, rfl⟩ := same
    rfl
  | .float ⟨negative, exponent, fraction⟩, second, same => by
    cases second <;> simp only [Term.identical, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    rename_i float
    obtain ⟨negative', exponent', fraction'⟩ := float
    obtain ⟨⟨rfl, exponent⟩, fraction⟩ := same
    rw [Fin.ext exponent, Fin.ext fraction]
  | .integer _, second, same | .atom _, second, same
  | .reference _, second, same | .pid _, second, same | .nil, second, same => by
    cases second <;> simp_all [Term.identical]

/-- Lists of identical terms are equal. -/
theorem Term.eq_of_identicalList : ∀ {first second : List Term},
    Term.identicalList first second = true → first = second
  | [], [], _ => rfl
  | head :: rest, head' :: rest', same => by
    simp only [Term.identicalList, Bool.and_eq_true] at same
    rw [Term.eq_of_identical same.1, Term.eq_of_identicalList same.2]
  | [], _ :: _, same | _ :: _, [], same => by simp [Term.identicalList] at same

/-- Lists of identical bindings are equal. -/
theorem Term.eq_of_identicalEntries : ∀ {first second : List (Term × Term)},
    Term.identicalEntries first second = true → first = second
  | [], [], _ => rfl
  | (key, value) :: rest, (key', value') :: rest', same => by
    simp only [Term.identicalEntries, Bool.and_eq_true] at same
    rw [Term.eq_of_identical same.1.1, Term.eq_of_identical same.1.2,
      Term.eq_of_identicalEntries same.2]
  | [], _ :: _, same | _ :: _, [], same => by simp [Term.identicalEntries] at same
end

end Lynx
