module

import Lynx.Modules.Erlang.lists
meta import LynxTest.ProofAudit

namespace LynxTest.Modules.Lists
open Lynx Erlang.lists

theorem reverse_empty (tail : Term) : «reverse/2» .nil tail = .ok tail := rfl

theorem reverse_onto_tail (a b tail : Term) :
    «reverse/2» (.cons a (.cons b .nil)) tail = .ok (.cons b (.cons a tail)) := by
  simp [«reverse/2»]

theorem reverse_improper (a tail : Term) :
    «reverse/2» (.cons a (.atom "improper")) tail = .error (.error (.atom "badarg")) := by
  simp [«reverse/2»]

theorem reverse_non_list (tail : Term) :
    «reverse/2» (.integer 1) tail = .error (.error (.atom "badarg")) := rfl

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.lists
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Lists

end LynxTest.Modules.Lists
