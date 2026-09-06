import LynxTest.Bench

set_option Elab.async false

namespace LynxBench

def nativeReverseAux {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => nativeReverseAux xs (x :: acc)

def nativeReverse {α : Type} (xs : List α) : List α := nativeReverseAux xs []

@[simp] theorem nativeReverseAux_spec {α : Type} (xs acc : List α) :
    nativeReverseAux (nativeReverseAux xs acc) [] = nativeReverseAux acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (x :: acc)

end LynxBench

open LynxBench

#bench "native/reverse-involution"
theorem native_reverse_involution_spec {α : Type} (xs : List α) :
    nativeReverse (nativeReverse xs) = xs := by
  exact nativeReverseAux_spec xs []

namespace LynxBench

/-- The accumulator is appended after reversing the input. -/
theorem nativeReverseAux_acc_spec {α : Type} (input acc : List α) :
    nativeReverseAux input acc = nativeReverse input ++ acc := by
  induction input generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    change nativeReverseAux tail (head :: acc) = nativeReverseAux tail [head] ++ acc
    rw [ih (head :: acc), ih [head], List.append_assoc]
    rfl

end LynxBench

#bench "native/reverse-append"
theorem native_reverse_append_spec {α : Type} (left right : List α) :
    nativeReverse (left ++ right) = nativeReverse right ++ nativeReverse left := by
  induction left with
  | nil => exact (List.append_nil _).symm
  | cons head tail ih =>
    change nativeReverseAux (tail ++ right) [head] =
      nativeReverse right ++ nativeReverseAux tail [head]
    rw [nativeReverseAux_acc_spec (tail ++ right), nativeReverseAux_acc_spec tail,
      ih, List.append_assoc]
