module

public import Init.Data.Ord.String
import all Init.Data.Ord.String

/-! Rules that let `cbv` evaluate closed programs. -/

public section

namespace Lynx.Term

/-- Atoms compare by name. Core implements string comparison natively, so
evaluation uses its definition through the order on strings. -/
@[cbv_eval] theorem string_compare_eq (left right : String) :
    String.compare left right = compareOfLessAndEq left right := by
  unfold String.compare
  rfl

end Lynx.Term
