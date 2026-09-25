module

public import Std

/-! Packed-bit operations exposed for reduction in proofs. -/

private instance : Repr ByteArray where
  reprPrec bytes prec := reprPrec bytes.data prec

namespace Lynx.Term.Bitstring

/-- Number of meaningful bits. Zero means the last byte is fully used;
otherwise only its leading `lastBits` bits are used. For empty storage the
count is ignored, and unused low bits never affect the represented value. -/
@[expose] public def bitSize (bytes : ByteArray) (lastBits : Fin 8) : Nat :=
  if bytes.size = 0 then 0
  else if lastBits = 0 then bytes.size * 8
  else (bytes.size - 1) * 8 + lastBits.val

/-- Meaningful bits in transmission order, most significant bit first.
This view also gives Erlang's lexicographic bitstring ordering. -/
@[expose] public def toBits (bytes : ByteArray) (lastBits : Fin 8) : List Bool :=
  (List.range (bitSize bytes lastBits)).map fun i =>
    (bytes[i / 8]!.toNat / 2 ^ (7 - i % 8)) % 2 == 1

end Lynx.Term.Bitstring
