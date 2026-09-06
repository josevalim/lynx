import Lynx

open Lean.Elab.Command

set_option Elab.async false

/-- Report elaboration time in milliseconds, including tactics but not imports. -/
elab "#bench " label:str declaration:command : command => do
  let start ← IO.monoNanosNow
  elabCommand declaration
  let elapsed := (← IO.monoNanosNow) - start
  let hundredths := (elapsed + 5000) / 10000
  let fraction := hundredths % 100
  let decimals := if fraction < 10 then s!"0{fraction}" else toString fraction
  Lean.logInfo m!"LYNX_BENCH {label.getString} {hundredths / 100}.{decimals}ms"
