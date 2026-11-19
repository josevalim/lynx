import LynxTest.ProofAudit
import Lynx.Concurrent.Forced
import Lynx.Concurrent.Trace
import Lynx.Concurrent.Termination
import Lynx.Concurrent.Confluence

/-! Axiom audits of the concurrent model, of `checkSleep`'s soundness proof,
of `check`'s, which rests on it, and of programs without races. -/

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Termination
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Commute
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Diamond
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Frames
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Sleep
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Forced
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Reduction
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Trace
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Confluence
  LynxTest.ProofAudit.checkDeclaration ``Lynx.Concurrent.checkSleep_sound
  LynxTest.ProofAudit.checkDeclaration ``Lynx.Concurrent.check_sound
  LynxTest.ProofAudit.checkDeclaration ``Lynx.Concurrent.RaceFree.of_talks
