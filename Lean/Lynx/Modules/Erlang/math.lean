module

public import Lynx.Purity

namespace Erlang.math
open Lynx

-- Both operations return a float. Keep the input sign when the result is zero,
-- including ceil of a negative fraction and either operation on negative zero.
private def roundFloat (up : Bool) (value : Term.FiniteFloat) : Except Exception Term :=
  -- At this exponent every binary64 value is already an integer. Returning
  -- its encoding avoids converting a potentially 1024-bit integer back again.
  if 1075 ≤ value.exponent.val then .ok (.float value)
  else
    let integer := if up then value.toRat.ceil else value.toRat.floor
    if integer = 0 then .ok (.float ⟨value.negative, 0, 0⟩)
    else
      match Term.FiniteFloat.ofInt integer with
      | some rounded => .ok (.float rounded)
      | none => .error (.error (.atom "badarith"))

private def roundNumber (up : Bool) : Term → Except Exception Term
  | .float value => roundFloat up value
  | .integer value =>
    match Term.FiniteFloat.ofInt value with
    | some converted => roundFloat up converted
    | none => .error (.error (.atom "badarith"))
  | _ => .error (.error (.atom "badarg"))

/-- Round down to an integral float, preserving signed zero. Integer arguments
are converted to binary64 first, as in the Erlang math BIF. -/
public def «floor/1» (value : Term) : Except Exception Term :=
  roundNumber false value

/-- Round up to an integral float, preserving signed zero. -/
public def «ceil/1» (value : Term) : Except Exception Term :=
  roundNumber true value

/-- Expose rounding of float arguments without exposing conversion helpers. -/
public theorem floor_float (value : Term.FiniteFloat) :
    «floor/1» (.float value) =
      if 1075 ≤ value.exponent.val then .ok (.float value)
      else if value.toRat.floor = 0 then .ok (.float ⟨value.negative, 0, 0⟩)
      else match Term.FiniteFloat.ofInt value.toRat.floor with
        | some rounded => .ok (.float rounded)
        | none => .error (.error (.atom "badarith")) := by rfl

public theorem ceil_float (value : Term.FiniteFloat) :
    «ceil/1» (.float value) =
      if 1075 ≤ value.exponent.val then .ok (.float value)
      else if value.toRat.ceil = 0 then .ok (.float ⟨value.negative, 0, 0⟩)
      else match Term.FiniteFloat.ofInt value.toRat.ceil with
        | some rounded => .ok (.float rounded)
        | none => .error (.error (.atom "badarith")) := by rfl

public theorem floor_large (value : Term.FiniteFloat) (large : 1075 ≤ value.exponent.val) :
    «floor/1» (.float value) = .ok (.float value) := by simp [floor_float, large]

public theorem ceil_large (value : Term.FiniteFloat) (large : 1075 ≤ value.exponent.val) :
    «ceil/1» (.float value) = .ok (.float value) := by simp [ceil_float, large]

end Erlang.math
