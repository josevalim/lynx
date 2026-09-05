import Benchmarks.Common

set_option Elab.async false

def nativeSum : List Int → Int
  | [] => 0
  | x :: xs => x + nativeSum xs

#bench "native/sum-append"
theorem native_sum_append (left right : List Int) :
    nativeSum left + nativeSum right = nativeSum (left ++ right) := by
  induction left <;> simp_all [nativeSum, Int.add_assoc]
