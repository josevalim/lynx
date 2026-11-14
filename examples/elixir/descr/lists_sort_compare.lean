namespace Elixir.STTDescrProofsTest.USort
open Lynx

/-! Abstract layer for `lists:usort/1` and `lists:ukeysort/2`: lists are compared by the
first element of each key (`lk`), and the merge states of OTP's merge sorts are described by
which sources remain and how they relate to the accumulated output. -/

theorem c_swap {a b : Term} : Term.compare (Term.fuel b a) b a = (Term.compare (Term.fuel a b) a b).swap :=
  Lynx.Term.compare_swap b a

theorem c_eq_symm {a b : Term} (h : Term.compare (Term.fuel a b) a b = .eq) : Term.compare (Term.fuel b a) b a = .eq :=
  Lynx.Term.compare_eq_symm h

theorem c_gt_of_lt {a b : Term} (h : Term.compare (Term.fuel a b) a b = .lt) : Term.compare (Term.fuel b a) b a = .gt :=
  Lynx.Term.compare_gt_of_lt h

theorem c_lt_of_gt {a b : Term} (h : Term.compare (Term.fuel a b) a b = .gt) : Term.compare (Term.fuel b a) b a = .lt :=
  Lynx.Term.compare_lt_of_gt h

theorem c_lt_trans {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .lt) (h₂ : Term.compare (Term.fuel b c) b c = .lt) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_trans h₁ h₂

theorem c_eq_trans {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .eq) (h₂ : Term.compare (Term.fuel b c) b c = .eq) :
    Term.compare (Term.fuel a c) a c = .eq := Lynx.Term.compare_eq_trans h₁ h₂

theorem c_lt_eq {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .lt) (h₂ : Term.compare (Term.fuel b c) b c = .eq) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_lt_of_eq h₁ h₂

theorem c_eq_lt {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .eq) (h₂ : Term.compare (Term.fuel b c) b c = .lt) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_eq_of_lt h₁ h₂

theorem c_lt_le {a b c : Term} (h₁ : Term.compare (Term.fuel a b) a b = .lt) (h₂ : (Term.compare (Term.fuel b c) b c).isLE) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_lt_of_isLE h₁ h₂

theorem c_le_lt {a b c : Term} (h₁ : (Term.compare (Term.fuel a b) a b).isLE) (h₂ : Term.compare (Term.fuel b c) b c = .lt) :
    Term.compare (Term.fuel a c) a c = .lt := Lynx.Term.compare_lt_of_isLE_of_lt h₁ h₂

theorem c_le_iff {a b : Term} : (Term.compare (Term.fuel a b) a b).isLE ↔ Term.compare (Term.fuel a b) a b ≠ .gt := by
  cases Term.compare (Term.fuel a b) a b <;> simp

theorem c_eq_ne_lt {a b : Term} (h : Term.compare (Term.fuel a b) a b = .eq) : Term.compare (Term.fuel a b) a b ≠ .lt := by
  simp [h]

section
variable (κ : Term → Term)

/-- The first element of `l` whose key compares equal to `s`. -/
def lk (s : Term) : List Term → Option Term
  | [] => none
  | x :: xs => if Term.compare (Term.fuel (κ x) s) (κ x) s = .eq then some x else lk s xs

/-- Two lists agree on the first element of every key. -/
def Eqv (A B : List Term) : Prop := ∀ s, lk κ s A = lk κ s B

/-- Strictly ascending keys. -/
def SA (l : List Term) : Prop := l.Pairwise (fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .lt)

/-- Strictly descending keys. -/
def SD (l : List Term) : Prop := l.Pairwise (fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) = .gt)

variable {κ}

@[simp] theorem lk_nil (s : Term) : lk κ s [] = none := rfl

theorem lk_cons (s x : Term) (xs : List Term) :
    lk κ s (x :: xs) = if Term.compare (Term.fuel (κ x) s) (κ x) s = .eq then some x else lk κ s xs := rfl

theorem lk_append (s : Term) (A B : List Term) : lk κ s (A ++ B) = (lk κ s A).or (lk κ s B) := by
  induction A with
  | nil => rfl
  | cons x xs ih => by_cases h : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq <;> simp [lk_cons, h, ih]

theorem lk_none {s : Term} {A : List Term} (h : ∀ x ∈ A, Term.compare (Term.fuel (κ x) s) (κ x) s ≠ .eq) :
    lk κ s A = none := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [lk_cons, h.1, ih h.2]

theorem lk_some {s y : Term} {A : List Term} (hy : y ∈ A) (h : Term.compare (Term.fuel (κ y) s) (κ y) s = .eq) :
    ∃ z, lk κ s A = some z := by
  induction A with
  | nil => simp at hy
  | cons x xs ih =>
    by_cases hx : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq
    · exact ⟨x, by simp [lk_cons, hx]⟩
    · simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact absurd h hx
      · simpa [lk_cons, hx] using ih hy

theorem Eqv.refl (A : List Term) : Eqv κ A A := fun _ => rfl
theorem Eqv.symm {A B : List Term} (h : Eqv κ A B) : Eqv κ B A := fun s => (h s).symm
theorem Eqv.trans {A B C : List Term} (h₁ : Eqv κ A B) (h₂ : Eqv κ B C) : Eqv κ A C :=
  fun s => (h₁ s).trans (h₂ s)
theorem Eqv.append {A A' B B' : List Term} (h₁ : Eqv κ A A') (h₂ : Eqv κ B B') :
    Eqv κ (A ++ B) (A' ++ B') := fun s => by simp [lk_append, h₁ s, h₂ s]
theorem Eqv.cons (x : Term) {A B : List Term} (h : Eqv κ A B) : Eqv κ (x :: A) (x :: B) :=
  Eqv.append (A := [x]) (A' := [x]) (Eqv.refl _) h

/-- An element can move to the front past elements of other keys. -/
theorem eqv_move {x : Term} {A B : List Term} (h : ∀ y ∈ A, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) ≠ .eq) :
    Eqv κ (A ++ x :: B) (x :: (A ++ B)) := by
  intro s
  by_cases hx : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq
  · have : lk κ s A = none := lk_none fun y hy hys => h y hy (c_eq_trans hys (c_eq_symm hx))
    simp [lk_append, lk_cons, hx, this]
  · simp [lk_append, lk_cons, hx]

/-- An element shadowed by an earlier one of the same key can be dropped. -/
theorem eqv_drop {x y : Term} {A B : List Term} (hy : y ∈ A) (h : Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .eq) :
    Eqv κ (A ++ x :: B) (A ++ B) := by
  intro s
  by_cases hx : Term.compare (Term.fuel (κ x) s) (κ x) s = .eq
  · obtain ⟨z, hz⟩ := lk_some hy (c_eq_trans h hx)
    simp [lk_append, hz]
  · simp [lk_append, lk_cons, hx]

theorem eqv_comm {A B : List Term} (h : ∀ x ∈ A, ∀ y ∈ B, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) ≠ .eq) :
    Eqv κ (A ++ B) (B ++ A) := by
  induction B generalizing A with
  | nil => simpa using Eqv.refl A
  | cons y ys ih =>
    have hy : ∀ x ∈ A, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) ≠ .eq := fun x hx => h x hx y (by simp)
    refine (eqv_move hy).trans (Eqv.cons y (ih fun x hx z hz => h x hx z (by simp [hz]))) |>.trans ?_
    simpa using Eqv.refl (y :: (ys ++ A))

theorem eqv_reverse {A : List Term} (h : A.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq) :
    Eqv κ A.reverse A := by
  induction A with
  | nil => exact Eqv.refl _
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    simp only [List.reverse_cons]
    refine (Eqv.append (ih h.2) (Eqv.refl [x])).trans ?_
    have := eqv_comm (κ := κ) (A := xs) (B := [x])
      (fun y hy z hz => by simp at hz; subst hz; intro e; exact h.1 y hy (c_eq_symm e))
    simpa using this

theorem SA.ne {l : List Term} (h : SA κ l) : l.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq :=
  h.imp fun e => by simp [e]

theorem SD.ne {l : List Term} (h : SD κ l) : l.Pairwise fun a b => Term.compare (Term.fuel (κ a) (κ b)) (κ a) (κ b) ≠ .eq :=
  h.imp fun e => by simp [e]

@[simp] theorem SA_nil : SA κ [] := List.Pairwise.nil
@[simp] theorem SD_nil : SD κ [] := List.Pairwise.nil

theorem SA_cons {x : Term} {l : List Term} :
    SA κ (x :: l) ↔ (∀ y ∈ l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) ∧ SA κ l := List.pairwise_cons

theorem SD_cons {x : Term} {l : List Term} :
    SD κ (x :: l) ↔ (∀ y ∈ l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .gt) ∧ SD κ l := List.pairwise_cons

theorem SA_reverse {l : List Term} : SA κ l.reverse ↔ SD κ l := by
  simp only [SA, SD, List.pairwise_reverse]
  exact ⟨fun h => h.imp c_gt_of_lt, fun h => h.imp c_lt_of_gt⟩

theorem SD_reverse {l : List Term} : SD κ l.reverse ↔ SA κ l := by
  simp only [SA, SD, List.pairwise_reverse]
  exact ⟨fun h => h.imp c_lt_of_gt, fun h => h.imp c_gt_of_lt⟩

/-- Every element of a strictly ascending list after a lower bound of its head. -/
theorem SA.lt_all {x b : Term} {l : List Term} (s : SA κ (b :: l))
    (h : Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b) = .lt) : ∀ y ∈ b :: l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · exact c_lt_trans h ((SA_cons.1 s).1 y hy)

theorem SA.le_all {x b : Term} {l : List Term} (s : SA κ (b :: l))
    (h : (Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b)).isLE) : ∀ y ∈ b :: l, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · have := c_le_lt h ((SA_cons.1 s).1 y hy); simp [this]

theorem SD.gt_all {x b : Term} {l : List Term} (s : SD κ (b :: l))
    (h : Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b) = .gt) : ∀ y ∈ b :: l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .gt := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · exact c_gt_of_lt (c_lt_trans (c_lt_of_gt ((SD_cons.1 s).1 y hy)) (c_lt_of_gt h))

theorem SD.ge_all {x b : Term} {l : List Term} (s : SD κ (b :: l))
    (h : Term.compare (Term.fuel (κ x) (κ b)) (κ x) (κ b) ≠ .lt) : ∀ y ∈ b :: l, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) ≠ .lt := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact h
  · exact fun e => h (c_lt_trans e (c_lt_of_gt ((SD_cons.1 s).1 y hy)))

end

end Elixir.STTDescrProofsTest.USort
