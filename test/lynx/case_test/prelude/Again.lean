module
public import Partial
public section
open Lean Elab Tactic

-- Parsing these declarations requires the syntax from `Partial`.
elab "test_partial_again" : tactic => do evalTactic (← `(tactic| test_partial))
elab "test_finish" : tactic => do evalTactic (← `(tactic| rfl))
