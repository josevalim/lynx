import LynxTest.Bench

set_option Elab.async false

namespace LynxBench

def reverse_aux_2 {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverse_aux_2 xs (x :: acc)

def reverse_1 {α : Type} (xs : List α) : List α := reverse_aux_2 xs []

@[simp] theorem native_reverse_aux_reverse {α : Type} (xs acc : List α) :
    reverse_aux_2 (reverse_aux_2 xs acc) [] = reverse_aux_2 acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (x :: acc)

end LynxBench

open LynxBench

#bench "native/reverse-involution"
theorem native_reverse_involution {α : Type} (xs : List α) :
    reverse_1 (reverse_1 xs) = xs := by
  exact native_reverse_aux_reverse xs []

namespace LynxBench

/-- The accumulator is appended after reversing the input. -/
theorem native_reverse_aux_acc {α : Type} (input acc : List α) :
    reverse_aux_2 input acc = reverse_1 input ++ acc := by
  induction input generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    change reverse_aux_2 tail (head :: acc) = reverse_aux_2 tail [head] ++ acc
    rw [ih (head :: acc), ih [head], List.append_assoc]
    rfl

end LynxBench

#bench "native/reverse-append"
theorem native_reverse_append {α : Type} (left right : List α) :
    reverse_1 (left ++ right) = reverse_1 right ++ reverse_1 left := by
  induction left with
  | nil => exact (List.append_nil _).symm
  | cons head tail ih =>
    change reverse_aux_2 (tail ++ right) [head] =
      reverse_1 right ++ reverse_aux_2 tail [head]
    rw [native_reverse_aux_acc (tail ++ right), native_reverse_aux_acc tail,
      ih, List.append_assoc]
