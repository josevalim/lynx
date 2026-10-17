module

import Lynx.Modules.Erlang.erts_internal
meta import LynxTest.ProofAudit
import Lynx

namespace LynxTest.Modules.ErtsInternal
open Lynx

private def a : Term := .atom "a"

/-- Map generators start from a fully expanded iterator; other terms yield `[]`,
which compiled comprehensions report as `bad_generator`. -/
theorem iterator_shapes :
    Erlang.erts_internal.«mc_iterator/1» (.map []) = .ok (.atom "none") ∧
    Erlang.erts_internal.«mc_iterator/1» (.cons a .nil) = .ok .nil ∧
    Erlang.erts_internal.«mc_iterator/1» a = .ok .nil := by
  refine ⟨?_, rfl, rfl⟩
  simp [Erlang.erts_internal.«mc_iterator/1»]

theorem iterator_entries (entries : List (Term × Term)) :
    Erlang.erts_internal.«mc_iterator/1» (.map entries) =
      .ok ((Term.mapEntries entries).foldr (fun entry rest => .tuple #[entry.1, entry.2, rest])
        (.atom "none")) := rfl

theorem refill_raises (iterator : Term) :
    Erlang.erts_internal.«mc_refill/1» iterator = .error (.error (.atom "badarg")) := rfl

end LynxTest.Modules.ErtsInternal

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erts_internal
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.ErtsInternal
