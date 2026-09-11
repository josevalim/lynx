module

public import Lynx.Term.DataTypes

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

private def compareMapViews (cmp : α → α → Ordering) : List (α × α) → List (α × α) → Ordering :=
  compareLex (compareOn Ord.compare List.length)
    (compareLex (compareOn (List.compareLex cmp) (List.map Prod.fst))
      (compareOn (List.compareLex cmp) (List.map Prod.snd)))

private instance (cmp : α → α → Ordering) [Std.TransCmp cmp] : Std.TransCmp (compareMapViews cmp) :=
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

@[simp] private theorem compareMapViews_map (cmp : β → β → Ordering) (f : α → β) (xs ys : List (α × α)) :
    compareMapViews cmp (xs.map (Prod.map f f)) (ys.map (Prod.map f f)) =
      compareMapViews (fun a b => cmp (f a) (f b)) xs ys := by
  simp [compareMapViews, compareLex, compareOn, List.map_map, ← lex_map, Function.comp_def, Prod.map]

end Lynx.Term.Compare

/-! ## Recursive comparison -/

namespace Lynx.Term.Compare

/-- One comparison step. The callback compares immediate children only. -/
private def compareStep (cmp : Term → Term → Ordering) : Term → Term → Ordering
  | .integer a, .integer b => Ord.compare a b
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .atom a, .atom b => Ord.compare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
  | .pid a, .pid b => Ord.compare a b
  | .pid _, _ => .lt
  | _, .pid _ => .gt
  | .tuple a, .tuple b =>
    (Ord.compare a.size b.size).then (List.compareLex cmp a.toList b.toList)
  | .tuple _, _ => .lt
  | _, .tuple _ => .gt
  | .map a, .map b => compareMapViews cmp (mapView cmp a) (mapView cmp b)
  | .map _, _ => .lt
  | _, .map _ => .gt
  | .nil, .nil => .eq
  | .nil, .cons _ _ => .lt
  | .cons _ _, .nil => .gt
  | .cons a as, .cons b bs => (cmp a b).then (cmp as bs)

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
private def boundedStep (n : Nat) (cmp : Child n → Child n → Ordering)
    (a b : Term) (ha : sizeOf a ≤ n) (hb : sizeOf b ≤ n) : Ordering :=
  match a, b with
  | .integer a, .integer b => Ord.compare a b
  | .integer _, _ => .lt
  | _, .integer _ => .gt
  | .atom a, .atom b => Ord.compare a b
  | .atom _, _ => .lt
  | _, .atom _ => .gt
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
    compareMapViews cmp (mapView cmp (boundedEntries n a (map_child ha)))
      (mapView cmp (boundedEntries n b (map_child hb)))
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

private theorem boundedStep_eq (n : Nat) (cmp : Term → Term → Ordering) (a b : Term)
    (ha : sizeOf a ≤ n) (hb : sizeOf b ≤ n) :
    boundedStep n (fun a b => cmp a.val b.val) a b ha hb = compareStep cmp a b := by
  cases a <;> cases b <;> simp only [boundedStep, compareStep]
  all_goals try rfl
  · rw [← lex_map cmp Subtype.val, boundedList_val, boundedList_val]
  · rw [← compareMapViews_map cmp Subtype.val, mapView_map, mapView_map,
      boundedEntries_val, boundedEntries_val]

end Lynx.Term.Compare

namespace Lynx.Term

/-- Erlang comparison, recursing only into children needed to decide the result.
Map comparison resolves shadowing and sorts outer bindings, without rebuilding
nested terms. The termination bound is erased from executable code. -/
@[semireducible] def compare (a b : Term) : Ordering :=
  Compare.boundedStep (max (sizeOf a) (sizeOf b))
    (fun x y => compare x.val y.val) a b (Nat.le_max_left _ _) (Nat.le_max_right _ _)
termination_by max (sizeOf a) (sizeOf b)
decreasing_by exact Nat.max_lt.mpr ⟨x.property, y.property⟩

private theorem compare_eq_step (a b : Term) : compare a b = Compare.compareStep compare a b := by
  rw [compare]
  exact Compare.boundedStep_eq _ _ _ _ _ _

end Lynx.Term

/-! ## Ordering laws -/

namespace Lynx.Term.Compare

private instance (cmp : Term → Term → Ordering) [Std.TransCmp cmp] : Std.TransCmp (compareStep cmp) where
  eq_swap := by
    intro a b
    cases a <;> cases b <;> simp only [compareStep, Ordering.swap_then,
      Ordering.swap_eq, Ordering.swap_lt, Ordering.swap_gt]
    all_goals try rfl
    all_goals first
      | exact Std.OrientedCmp.eq_swap
      | (congr 1 <;> exact Std.OrientedCmp.eq_swap)
  isLE_trans := by
    intro a b c ab bc
    cases a <;> cases b <;> cases c <;>
      simp only [compareStep, Ordering.isLE_lt, Ordering.isLE_eq, Ordering.isLE_gt,
        Bool.false_eq_true] at ab bc ⊢
    all_goals try contradiction
    all_goals try trivial
    all_goals try exact Std.TransCmp.isLE_trans ab bc
    case tuple.tuple.tuple a b c =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn Ord.compare Array.size) (compareOn (List.compareLex cmp) Array.toList)) ab bc
    case cons.cons.cons ah ats bh bt ch ct =>
      exact Std.TransCmp.isLE_trans
        (cmp := compareLex (compareOn cmp Prod.fst) (compareOn cmp Prod.snd))
        (a := (ah,ats)) (b := (bh,bt)) (c := (ch,ct)) ab bc

/-- Finite approximations used only to prove ordering laws. Executable comparison
uses well-founded recursion, not a runtime depth counter. -/
private def approximation : Nat → Term → Term → Ordering
  | 0 => fun _ _ => .eq
  | n + 1 => compareStep (approximation n)

private instance approximation_trans (n : Nat) : Std.TransCmp (approximation n) := by
  induction n with
  | zero => exact { eq_swap := by intros; rfl, isLE_trans := by intros; rfl }
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Std.TransCmp (compareStep (approximation n)))

private theorem compare_eq_approximation (n : Nat) (a b : Term)
    (h : max (sizeOf a) (sizeOf b) ≤ n) : Term.compare a b = approximation n a b := by
  induction n generalizing a b with
  | zero => cases a <;> simp_all <;> omega
  | succ n ih =>
    rw [Term.compare, approximation,
      ← boundedStep_eq (max (sizeOf a) (sizeOf b)) (approximation n) a b
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)]
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

/-! ## Semantic equality -/

namespace Lynx.Term

/-- Erlang equality is the equality case of recursive term comparison. -/
@[expose] def Equivalent (a b : Term) : Prop := compare a b = .eq

instance (a b : Term) : Decidable (Equivalent a b) := inferInstanceAs (Decidable (_ = _))

@[refl, simp] theorem equivalent_refl (a : Term) : Equivalent a a := compare_self a
@[symm] theorem equivalent_symm {a b : Term} (h : Equivalent a b) : Equivalent b a := Std.OrientedCmp.eq_symm h
theorem equivalent_trans {a b c : Term} (h : Equivalent a b) (h' : Equivalent b c) :
    Equivalent a c := Std.TransCmp.eq_trans h h'

@[simp] theorem compare_eq_nil (a : Term) : compare a .nil = .eq ↔ a = .nil := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem nil_compare_eq (a : Term) : compare .nil a = .eq ↔ a = .nil := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_nil a
@[simp] theorem compare_eq_integer (a : Term) (n : Int) :
    compare a (.integer n) = .eq ↔ a = .integer n := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem integer_compare_eq (n : Int) (a : Term) :
    compare (.integer n) a = .eq ↔ a = .integer n := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_integer a n
@[simp] theorem compare_eq_atom (a : Term) (s : String) :
    compare a (.atom s) = .eq ↔ a = .atom s := by
  cases a <;> rw [compare_eq_step] <;> simp [Compare.compareStep]
@[simp] theorem atom_compare_eq (s : String) (a : Term) :
    compare (.atom s) a = .eq ↔ a = .atom s := by
  rw [compare_swap, Ordering.swap_eq_eq]
  exact compare_eq_atom a s
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
instance : BEq Term := ⟨fun a b => decide (Term.Equivalent a b)⟩

@[simp] theorem Term.beq_iff_equivalent (a b : Term) :
    (a == b) = true ↔ Term.Equivalent a b := by
  change decide (Term.Equivalent a b) = true ↔ _
  simp

instance : EquivBEq Term where
  rfl := by intro a; exact (Term.beq_iff_equivalent a a).mpr (Term.equivalent_refl a)
  symm := by
    intro a b h
    exact (Term.beq_iff_equivalent b a).mpr (Term.equivalent_symm ((Term.beq_iff_equivalent a b).mp h))
  trans := by
    intro a b c h h'
    exact (Term.beq_iff_equivalent a c).mpr
      (Term.equivalent_trans ((Term.beq_iff_equivalent a b).mp h) ((Term.beq_iff_equivalent b c).mp h'))

end Lynx

namespace Lynx.Term

/-- Ordering equality is semantic equality; association-list storage need not match. -/
theorem compare_eq (a b : Term) : compare a b = .eq ↔ Equivalent a b := Iff.rfl

theorem compare_congr {a b c d : Term} (ha : Equivalent a b) (hb : Equivalent c d) :
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
private theorem compareMapViews_eq_of_lookup (a b : List (α × α))
    (ha : MapViewSorted cmp a) (hb : MapViewSorted cmp b)
    (h : ∀ q, Option.Rel (fun a b => cmp a b = .eq) (mapViewLookup cmp a q) (mapViewLookup cmp b q)) :
    compareMapViews cmp a b = .eq := by
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
      have values : cmp e.2 f.2 = .eq := by
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

/-- Singleton maps compare their keys before their values. -/
theorem compare_singleton_map (k v l w : Term) :
    compare (.map [(k,v)]) (.map [(l,w)]) = (compare k l).then (compare v w) := by
  rw [compare_eq_step]
  simp [Compare.compareStep, Compare.mapView, Compare.mapViewInsert, Compare.compareMapViews,
    compareLex, Compare.compareOn,
    List.compareLex_cons_cons, List.compareLex_nil_nil]

/-- Matching first-binding lookups suffice for semantic map equality. -/
theorem map_equivalent_of_lookup (a b : List (Term × Term))
    (h : ∀ q, Option.Rel Equivalent
      ((a.find? fun e => decide (compare q e.1 = .eq)).map Prod.snd)
      ((b.find? fun e => decide (compare q e.1 = .eq)).map Prod.snd)) :
    Equivalent (.map a) (.map b) := by
  rw [Equivalent, compare_eq_step]
  apply Compare.compareMapViews_eq_of_lookup _ _ _
    (Compare.mapView_sorted _ _) (Compare.mapView_sorted _ _)
  intro q
  simp only [Compare.mapViewLookup_view]
  exact h q

end Lynx.Term
