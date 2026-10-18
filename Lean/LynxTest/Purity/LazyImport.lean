module

import LynxTest.Purity.Lazy
meta import LynxTest.ProofAudit

/-! Lemmas generated on demand are realized in the importing module. -/

namespace LynxTest.Purity.LazyImport
open Lynx LynxTest.Purity.Lazy

theorem each_partial (a : Term) : Result.IsPartial («lazyEach/1» a) := by simp
theorem rotateThird_partial (left right : Term) : Result.IsPartial (lazyRotateThird left right) := by simp
theorem classify_partial (input : Term) : Result.IsPartial (lazyClassify input) := by simp

theorem nodes_partial (t : Term) : Result.IsPartial (lazyNodes t) := by simp

theorem items_partial (a b : Term) : Result.IsPartial (lazyItems a b) := by simp

end LynxTest.Purity.LazyImport

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Purity.LazyImport
