module

public import Lean

public section

/-! Reusable proof checks. Audit calls belong in the corresponding test modules;
integration audits live in `LynxTest.Integration`, outside benchmark source files. -/
namespace LynxTest.ProofAudit
open Lean

/-- Kernel axioms accepted by the project's proofs; `sorryAx` is excluded. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def declarationInfo (name : Name) : Elab.Command.CommandElabM ConstantInfo := do
  let some info := ((← getEnv).setExporting false).find? name
    | throwError "unknown audit declaration: {name}"
  return info

/-- Check all axioms used by a declaration, including its transitive dependencies. -/
def checkDeclaration (name : Name) (allowed : Array Name := standardAxioms) : Elab.Command.CommandElabM Unit := do
  let _ ← declarationInfo name
  for axiomName in ← collectAxioms name do
    unless allowed.contains axiomName do
      throwError "unexpected axiom in {name}: {axiomName}"

/-- Select declarations by their defining module, including private declarations
and instances regardless of namespace. The current module includes declarations
elaborated before this call; place its audit at the end of the file. -/
def moduleDeclarations (moduleName : Name) : Elab.Command.CommandElabM (Array Name) := do
  let env := (← getEnv).setExporting false
  let moduleIdx := env.getModuleIdx? moduleName
  unless moduleName == env.mainModule || moduleIdx.isSome do
    throwError "unknown audit module: {moduleName}"
  let names := env.constants.toList.filterMap fun (name, _) =>
    -- Kernel caches can retain auxiliary declarations from rolled-back tactic branches.
    if (env.find? name).isSome && env.getModuleIdxFor? name == moduleIdx then some name else none
  if names.isEmpty then throwError "audit module has no declarations: {moduleName}"
  return names.toArray

/-- Audit a whole module with the same axiom policy as a single declaration. -/
def checkModule (moduleName : Name) (allowed : Array Name := standardAxioms) : Elab.Command.CommandElabM Unit := do
  for name in ← moduleDeclarations moduleName do
    checkDeclaration name allowed

/-- Reject reuse of forbidden declarations, including reuse through helper definitions. -/
def checkNoDependencies (name : Name) (forbidden : Array Name) : Elab.Command.CommandElabM Unit := do
  let info ← declarationInfo name
  let some proof := info.value? (allowOpaque := true)
    | throwError "expected a definition or theorem body: {name}"
  for dependency in forbidden do
    let _ ← declarationInfo dependency
  let mut pending := proof.getUsedConstants
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let dependency := pending.back!
    pending := pending.pop
    if forbidden.contains dependency then
      throwError "{name} depends on forbidden declaration {dependency}"
    if visited.contains dependency then continue
    visited := visited.insert dependency
    let info ← declarationInfo dependency
    if let some body := info.value? (allowOpaque := true) then
      pending := pending ++ body.getUsedConstants

/-- Each selected target must prove its result without reusing another target. -/
def checkIndependent (names : Array Name) : Elab.Command.CommandElabM Unit := do
  for name in names do
    checkNoDependencies name (names.filter (· != name))

end LynxTest.ProofAudit

/-! Regression checks for the audit helpers themselves. -/

-- Deliberately use a namespace unrelated to the module name.
namespace AuditFixture
private theorem propositionalEquality : (True ∧ True) = True :=
  propext ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩

private theorem original : True := True.intro
private def bridge : {_n : Nat // True} := ⟨0, original⟩
private theorem indirect : True := bridge.property
private theorem independent : True := True.intro
end AuditFixture

namespace LynxTest.ProofAudit
open Lean Elab.Command

private def expectFailure (action : CommandElabM Unit) : CommandElabM Unit := do
  let failed ← try action; pure false catch _ => pure true
  unless failed do throwError "expected the audit to reject this input"

run_cmd do
  checkDeclaration ``AuditFixture.original #[]
  checkDeclaration ``AuditFixture.propositionalEquality
  expectFailure (checkDeclaration ``AuditFixture.propositionalEquality #[])
  expectFailure (checkDeclaration `MissingAuditDeclaration)
  expectFailure (checkModule `MissingAuditModule)

  let localNames ← moduleDeclarations `LynxTest.ProofAudit
  unless localNames.contains ``AuditFixture.propositionalEquality do
    throwError "module audit omitted a private theorem in a different namespace"
  let importedNames ← moduleDeclarations `Lean.Util.CollectAxioms
  unless importedNames.contains ``Lean.collectAxioms && !importedNames.contains ``AuditFixture.original do
    throwError "module audit did not isolate the defining module"
  checkModule `LynxTest.ProofAudit
  expectFailure (checkModule `LynxTest.ProofAudit #[])

  checkNoDependencies ``AuditFixture.independent #[``AuditFixture.original]
  expectFailure (checkNoDependencies ``AuditFixture.indirect #[``AuditFixture.original])
  checkIndependent #[``AuditFixture.original, ``AuditFixture.independent]
  expectFailure (checkIndependent #[``AuditFixture.original, ``AuditFixture.indirect])

end LynxTest.ProofAudit
