import LynxTest.Bench

set_option Elab.async false

namespace LynxBench

def native_reverse_aux {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => native_reverse_aux xs (x :: acc)

def nativeReverse {α : Type} (xs : List α) : List α := native_reverse_aux xs []

@[simp] theorem native_reverse_aux_reverse {α : Type} (xs acc : List α) :
    native_reverse_aux (native_reverse_aux xs acc) [] = native_reverse_aux acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (x :: acc)

end LynxBench

open LynxBench

#bench "native/reverse-involution"
theorem native_reverse_involution {α : Type} (xs : List α) :
    nativeReverse (nativeReverse xs) = xs := by
  exact native_reverse_aux_reverse xs []

namespace LynxBench

/-- The accumulator is appended after reversing the input. -/
theorem native_reverse_aux_acc {α : Type} (input acc : List α) :
    native_reverse_aux input acc = nativeReverse input ++ acc := by
  induction input generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    change native_reverse_aux tail (head :: acc) = native_reverse_aux tail [head] ++ acc
    rw [ih (head :: acc), ih [head], List.append_assoc]
    rfl

end LynxBench

#bench "native/reverse-append"
theorem native_reverse_append {α : Type} (left right : List α) :
    nativeReverse (left ++ right) = nativeReverse right ++ nativeReverse left := by
  induction left with
  | nil => exact (List.append_nil _).symm
  | cons head tail ih =>
    change native_reverse_aux (tail ++ right) [head] =
      nativeReverse right ++ native_reverse_aux tail [head]
    rw [native_reverse_aux_acc (tail ++ right), native_reverse_aux_acc tail,
      ih, List.append_assoc]
