module

public section

/-! List functions written with `List.rec`, for definitions the kernel evaluates in proofs
(`Lynx.Concurrent.check`). The kernel unfolds core's structural recursion through
`List.brecOn`, which costs much more per element. Each equals its core function:
`@[csimp]` keeps compiled code on core's, and `simp` rewrites to it in proofs. -/

namespace Lynx.Concurrent.Kernel

universe u v

@[expose] noncomputable def append {α : Type u} (first second : List α) : List α :=
  @List.rec α (fun _ => List α) second (fun head _ rest => head :: rest) first

@[expose] noncomputable def filter {α : Type u} (p : α → Bool) (l : List α) : List α :=
  @List.rec α (fun _ => List α) [] (fun head _ rest => cond (p head) (head :: rest) rest) l

@[expose] noncomputable def find? {α : Type u} (p : α → Bool) (l : List α) : Option α :=
  @List.rec α (fun _ => Option α) none (fun head _ rest => cond (p head) (some head) rest) l

@[expose] noncomputable def any {α : Type u} (l : List α) (p : α → Bool) : Bool :=
  @List.rec α (fun _ => Bool) false (fun head _ rest => cond (p head) true rest) l

@[expose] noncomputable def all {α : Type u} (l : List α) (p : α → Bool) : Bool :=
  @List.rec α (fun _ => Bool) true (fun head _ rest => cond (p head) rest false) l

@[expose] noncomputable def map {α : Type u} {β : Type v} (f : α → β) (l : List α) : List β :=
  @List.rec α (fun _ => List β) [] (fun head _ rest => f head :: rest) l

@[expose] noncomputable def filterMap {α : Type u} {β : Type v} (f : α → Option β)
    (l : List α) : List β :=
  @List.rec α (fun _ => List β) []
    (fun head _ rest => @Option.casesOn β (fun _ => List β) (f head) rest (· :: rest)) l

@[expose] noncomputable def foldl {α : Type u} {β : Type v} (f : α → β → α) (init : α)
    (l : List β) : α :=
  @List.rec β (fun _ => α → α) id (fun head _ rest acc => rest (f acc head)) l init

@[expose] noncomputable def lookup {α : Type u} {β : Type v} [BEq α] (key : α)
    (l : List (α × β)) : Option β :=
  @List.rec (α × β) (fun _ => Option β) none
    (fun head _ rest => cond (key == head.1) (some head.2) rest) l

@[expose] noncomputable def contains {α : Type u} [BEq α] (l : List α) (a : α) : Bool :=
  @List.rec α (fun _ => Bool) false (fun head _ rest => cond (a == head) true rest) l

@[expose] noncomputable def eraseP {α : Type u} (p : α → Bool) (l : List α) : List α :=
  @List.rec α (fun _ => List α) [] (fun head tail rest => cond (p head) tail (head :: rest)) l

@[expose] noncomputable def erase {α : Type u} [BEq α] (l : List α) (a : α) : List α :=
  @List.rec α (fun _ => List α) [] (fun head tail rest => cond (head == a) tail (head :: rest)) l

@[expose] noncomputable def length {α : Type u} (l : List α) : Nat :=
  @List.rec α (fun _ => Nat) 0 (fun _ _ rest => rest + 1) l

@[expose] noncomputable def flatMap {α : Type u} {β : Type v} (f : α → List β) (l : List α) :
    List β :=
  @List.rec α (fun _ => List β) [] (fun head _ rest => append (f head) rest) l

@[csimp] theorem append_eq_append : @append = @List.append := by
  funext α first second; induction first with
  | nil => rfl
  | cons head tail ih => rw [List.append, ← ih]; rfl

@[simp] theorem append_eq {α : Type u} (first second : List α) :
    append first second = first ++ second := by
  rw [append_eq_append]; rfl

@[csimp, simp] theorem filter_eq : @filter = @List.filter := by
  funext α p l; induction l with
  | nil => rfl
  | cons head tail ih => rw [List.filter, ← ih]; rfl

@[csimp, simp] theorem find?_eq : @find? = @List.find? := by
  funext α p l; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.find?, ← ih]
    show cond (p head) _ _ = _; cases p head <;> rfl

@[csimp, simp] theorem any_eq : @any = @List.any := by
  funext α l p; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.any, ← ih]
    show cond (p head) _ _ = _; cases p head <;> rfl

@[csimp, simp] theorem all_eq : @all = @List.all := by
  funext α l p; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.all, ← ih]
    show cond (p head) _ _ = _; cases p head <;> rfl

@[csimp, simp] theorem map_eq : @map = @List.map := by
  funext α β f l; induction l with
  | nil => rfl
  | cons head tail ih => rw [List.map, ← ih]; rfl

@[csimp, simp] theorem filterMap_eq : @filterMap = @List.filterMap := by
  funext α β f l; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.filterMap, ← ih]
    show @Option.casesOn β (fun _ => List β) (f head) _ _ = _; cases f head <;> rfl

@[csimp, simp] theorem foldl_eq : @foldl = @List.foldl := by
  funext α β f init l; induction l generalizing init with
  | nil => rfl
  | cons head tail ih => rw [List.foldl, ← ih]; rfl

@[csimp, simp] theorem lookup_eq : @lookup = @List.lookup := by
  funext α β _ key l; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.lookup, ← ih]
    show cond (key == head.1) _ _ = _; cases key == head.1 <;> rfl

@[csimp, simp] theorem contains_eq : @contains = @List.contains := by
  funext α _ l a; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.contains, List.elem, ← List.contains, ← ih]
    show cond (a == head) _ _ = _; cases a == head <;> rfl

@[csimp, simp] theorem eraseP_eq : @eraseP = @List.eraseP := by
  funext α p l; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.eraseP, ← ih]
    show cond (p head) _ _ = _; cases p head <;> rfl

@[csimp, simp] theorem erase_eq : @erase = @List.erase := by
  funext α _ l a; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.erase, ← ih]
    show cond (head == a) _ _ = _; cases head == a <;> rfl

@[csimp, simp] theorem length_eq : @length = @List.length := by
  funext α l; induction l with
  | nil => rfl
  | cons head tail ih => rw [List.length, ← ih]; rfl

@[csimp, simp] theorem flatMap_eq : @flatMap = @List.flatMap := by
  funext α β f l; induction l with
  | nil => rfl
  | cons head tail ih =>
    rw [List.flatMap_cons, ← ih]
    show append (f head) (flatMap f tail) = _; rw [append_eq]

/-- Equality of PIDs and references, by `List.rec` and `Nat.beq`. -/
@[expose] noncomputable def pidEq (first second : List Nat) : Bool :=
  @List.rec Nat (fun _ => List Nat → Bool)
    (fun other => @List.casesOn Nat (fun _ => Bool) other true (fun _ _ => false))
    (fun head _ rest other => @List.casesOn Nat (fun _ => Bool) other false
      (fun head' tail' => Nat.beq head head' && rest tail'))
    first second

theorem pidEq_iff : ∀ first second : List Nat, pidEq first second = true ↔ first = second
  | [], [] => by simp [pidEq]
  | [], _ :: _ => by simp [pidEq]
  | _ :: _, [] => by simp [pidEq]
  | head :: tail, head' :: tail' => by
      have ih := pidEq_iff tail tail'
      change (Nat.beq head head' && pidEq tail tail') = true ↔ _
      simp [ih, Nat.beq_eq_true_eq]

/-- Core's equality of lists of naturals, which compiled code uses. -/
@[expose] def stdEq (first second : List Nat) : Bool := first == second

@[csimp] theorem pidEq_eq_stdEq : @pidEq = @stdEq := by
  funext first second
  cases h : stdEq first second with
  | true => exact (pidEq_iff _ _).2 (by simpa [stdEq] using h)
  | false =>
      cases h' : pidEq first second with
      | false => rfl
      | true => have := (pidEq_iff _ _).1 h'; subst this; simp [stdEq] at h

@[expose] def pidBEq : BEq (List Nat) := ⟨pidEq⟩

instance pidRefl : @ReflBEq (List Nat) pidBEq :=
  @ReflBEq.mk (List Nat) pidBEq (fun {a} => (pidEq_iff a a).2 rfl)

instance pidLawful : @LawfulBEq (List Nat) pidBEq :=
  @LawfulBEq.mk (List Nat) pidBEq pidRefl (fun h => (pidEq_iff _ _).1 h)

end Lynx.Concurrent.Kernel
end
