module
public import Lynx
public section
open Lean Elab Tactic
elab "test_finish" : tactic => throwError "second prelude loaded"
