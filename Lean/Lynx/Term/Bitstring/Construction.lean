module

public import Lynx.Pure
public import Lynx.Term.Bitstring

namespace Lynx.Term.Bitstring

/-- Pack transmission-order bits as a term. The empty list produces the empty binary. -/
@[expose] public def ofBits (bits : List Bool) : Term :=
  .bitstring (pack bits) ⟨bits.length % 8, Nat.mod_lt _ (by decide)⟩ (by
    intro empty
    have size := pack_size bits
    apply Fin.ext
    simp only [Fin.val_zero]
    omega)

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

/-- Concatenate meaningful bits, including segments that cross byte boundaries. -/
#lynx_pure @[expose] public def append (left right : Term) : Result :=
  match left, right with
  | .bitstring a ab _, .bitstring b bb _ =>
      .ok (ofBits (toBits a ab ++ toBits b bb))
  | _, _ => .error (.error (.atom "badarg"))

end Lynx.Term.Bitstring
