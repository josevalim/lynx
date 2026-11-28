module

public import Lynx

public section

namespace TaskProof

/-! `cbv` cannot decide `n * 2 < n * 2` for a symbolic `n`, so it compares
a number with itself by these lemmas instead. -/

@[cbv_eval] theorem compare_int_self (a : Int) : compareOfLessAndEq a a = .eq := by
  simp [compareOfLessAndEq]

@[cbv_eval] theorem compare_rat_self (a : Rat) : compareOfLessAndEq a a = .eq := by
  simp [compareOfLessAndEq]

end TaskProof
