import LynxTest.Bench

set_option Elab.async false

namespace LynxBench

def nativeReverseAux {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => nativeReverseAux xs (x :: acc)

def nativeReverse {α : Type} (xs : List α) : List α := nativeReverseAux xs []

@[simp] theorem nativeReverseAux_spec {α : Type} (xs acc : List α) :
    nativeReverseAux xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change nativeReverseAux xs (x :: acc) = _
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

end LynxBench

open LynxBench

#bench "native/reverse-correctness"
theorem native_reverse_spec {α : Type} (xs : List α) : nativeReverse xs = xs.reverse := by
  simp [nativeReverse]

#bench "native/reverse-involution"
theorem native_reverse_involution_spec {α : Type} (xs : List α) :
    nativeReverse (nativeReverse xs) = xs := by
  simp [nativeReverse]
