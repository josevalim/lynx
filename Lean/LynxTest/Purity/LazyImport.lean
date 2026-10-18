module

import LynxTest.Purity.Lazy
meta import LynxTest.ProofAudit

/-! Lemmas generated on demand are realized in the importing module. -/

namespace LynxTest.Purity.LazyImport
open Lynx LynxTest.Purity.Lazy

theorem each_partial (a : Term) : Result.IsPartial («lazyEach/1» a) := by simp
theorem rotateThird_pure (left right : Term) : Result.IsPure (lazyRotateThird left right) := by simp
-- Pure lemmas also close partiality goals.
theorem classify_partial (input : Term) : Result.IsPartial (lazyClassify input) := by simp

theorem nodes_pure (t : Term) : Result.IsPure (lazyNodes t) := by simp

theorem items_pure (a b : Term) : Result.IsPure (lazyItems a b) := by simp

end LynxTest.Purity.LazyImport

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Purity.LazyImport
