module

public import Lynx.Term.Bitstring.Construction

namespace Lynx.Term.Bitstring

/-- Extract an integer and leave the unconsumed bits. Invalid sizes, operand
kinds, and short inputs fail the pattern rather than raising an exception. -/
@[expose] public def matchInteger (input size : Term) (unit : Nat)
    (signed little : Bool) : Option (Term × Term) :=
  match input, size with
  | .bitstring bytes last _, .integer size =>
    if 0 ≤ size ∧ 1 ≤ unit ∧ unit ≤ 256 then
      let bits := toBits bytes last
      let width := size.toNat * unit
      if width ≤ bits.length then
        let value := decodeInteger (bits.take width) little
        let integer := if signed && width > 0 && value ≥ 2 ^ (width - 1)
          then Int.ofNat value - (2 : Int) ^ width else Int.ofNat value
        some (.integer integer, ofBits (bits.drop width))
      else none
    else none
  | _, _ => none

/-- Extract a finite binary64 float. Non-finite encodings fail the pattern.
Binary16 and binary32 decoding are not implemented yet. -/
@[expose] public def matchFloat (input : Term) (width : Nat) (little : Bool) :
    Option (Term × Term) := do
  if width != 64 then none else do
    let (.integer value, rest) ← matchInteger input (.integer 64) 1 Bool.false little | none
    let encoded := value.toNat
    let exponent := encoded / 2 ^ 52 % 2048
    if h : exponent < 2047 then
      some (.float ⟨encoded / 2 ^ 63 != 0, ⟨exponent, h⟩,
        ⟨encoded % 2 ^ 52, Nat.mod_lt _ (by decide)⟩⟩, rest)
    else none

/-- Validate a trailing binary or bitstring. The segment's unit constrains its
length; binary uses eight and bitstring uses one. Alignment is relative to the
captured segment, so an unaligned start is allowed. Explicit sizes must
consume exactly the remaining bits. -/
@[expose] public def matchTail (input size : Term) (unit : Nat) : Bool :=
  match input with
  | .bitstring bytes last _ =>
    if 1 ≤ unit ∧ unit ≤ 256 then
      match size with
      | .atom "all" => bitSize bytes last % unit == 0
      | .integer width => decide (0 ≤ width ∧ bitSize bytes last = width.toNat * unit)
      | _ => Bool.false
    else Bool.false
  | _ => Bool.false

/-- A pattern without a trailing capture must consume the whole bitstring. -/
@[expose] public def matchEnd (input : Term) : Bool :=
  match input with
  | .bitstring bytes last _ => bitSize bytes last == 0
  | _ => Bool.false

end Lynx.Term.Bitstring
