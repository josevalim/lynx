module

public import Lynx.Pure
public import Lynx.Term.Bitstring

namespace Lynx.Term.Bitstring

/-- Pack transmission-order bits as a term. The empty list produces the empty binary. -/
@[expose] public def ofBits (bits : List Bool) : Term :=
  .bitstring (pack bits) ⟨bits.length % 8, Nat.mod_lt _ (by decide)⟩ (pack_valid bits)

/-- Packing preserves the number of meaningful bits. -/
@[simp] public theorem ofBits_bitSize (bits : List Bool) :
    (match ofBits bits with
      | .bitstring bytes last _ => bitSize bytes last
      | _ => 0) = bits.length := by
  exact pack_bitSize bits

/-- Packing preserves every bit in transmission order. -/
@[simp] public theorem ofBits_toBits (bits : List Bool) :
    (match ofBits bits with
      | .bitstring bytes last _ => toBits bytes last
      | _ => []) = bits := by
  exact pack_toBits bits

/-- Build an integer segment. Segment sizes count `unit` bits and must be
nonnegative integers; the Core unit is a compile-time value in `1..256`. -/
#lynx_pure @[expose] public def integerSegment (value size : Term) (unit : Nat)
    (little : Bool) : Result :=
  match value, size with
  | .integer value, .integer size =>
    if 0 ≤ size ∧ 1 ≤ unit ∧ unit ≤ 256 then
      .ok (ofBits (integerBits value (size.toNat * unit) little))
    else .error (.error (.atom "badarg"))
  | _, _ => .error (.error (.atom "badarg"))

/-- Encode binary64 fields without rounding. Integer operands are first rounded
into binary64, failing with badarg if conversion overflows. Binary16 and
binary32 are not modeled yet and currently return badarg. -/
#lynx_pure @[expose] public def floatSegment (value : Term) (width : Nat) (little : Bool) : Result :=
  if width != 64 then .error (.error (.atom "badarg"))
  else
    let converted := match value with
      | .float value => some value
      | .integer value => Term.FiniteFloat.ofInt value
      | _ => none
    match converted with
    | some value =>
      let encoded : Nat := (if value.negative then 2 ^ 63 else 0) +
        value.exponent.val * 2 ^ 52 + value.fraction.val
      integerSegment (.integer (Int.ofNat encoded)) (.integer 64) 1 little
    | none => .error (.error (.atom "badarg"))

/-- Concatenate meaningful bits, including segments that cross byte boundaries. -/
#lynx_pure @[expose] public def append (left right : Term) : Result :=
  match left, right with
  | .bitstring a ab _, .bitstring b bb _ =>
      .ok (ofBits (toBits a ab ++ toBits b bb))
  | _, _ => .error (.error (.atom "badarg"))

end Lynx.Term.Bitstring
