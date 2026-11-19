import LynxTest.ProofAudit
import Lynx.Concurrent.Forced

/-! Axiom audits of the concurrent model and of `checkSleep`'s soundness proof,
which no runtime module imports yet. -/

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Commute
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Diamond
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Frames
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Sleep
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Forced
  LynxTest.ProofAudit.checkDeclaration ``Lynx.Concurrent.checkSleep_sound
