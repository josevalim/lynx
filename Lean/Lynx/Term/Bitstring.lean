module

public import Std

/-! Packed-bit operations exposed for reduction in proofs. -/

private instance : Repr ByteArray where
  reprPrec bytes prec := reprPrec bytes.data prec

namespace Lynx.Term.Bitstring

/-- Number of meaningful bits. Zero means the last byte is fully used;
otherwise only its leading `lastBits` bits are used. Empty storage has zero
meaningful bits; `Term` requires its count to be zero. Unused low bits never
affect the represented value. -/
@[expose] public def bitSize (bytes : ByteArray) (lastBits : Fin 8) : Nat :=
  if bytes.size = 0 then 0
  else if lastBits = 0 then bytes.size * 8
  else (bytes.size - 1) * 8 + lastBits.val

/-- Meaningful bits in transmission order, most significant bit first.
This view also gives Erlang's lexicographic bitstring ordering. -/
@[expose] public def toBits (bytes : ByteArray) (lastBits : Fin 8) : List Bool :=
  (List.range (bitSize bytes lastBits)).map fun i =>
    bytes[i / 8]!.toBitVec.getMsbD (i % 8)

/-- Integer segments truncate to their low `width` bits, including negative
values. Little endian emits low bytes first, then any remaining high bits.
Signedness affects matching, but does not affect construction. -/
@[expose] public def integerBits (value : Int) (width : Nat) (little : Bool) : List Bool :=
  (List.range width).map fun i =>
    let shift := if little then
      i / 8 * 8 + (min 8 (width - i / 8 * 8) - 1 - i % 8)
    else width - 1 - i
    (value >>> shift) % 2 == 1

/-- Pack transmission-order bits into bytes, padding unused low bits with zero. -/
@[expose] public def pack (bits : List Bool) : ByteArray :=
  ⟨((List.range ((bits.length + 7) / 8)).map fun index =>
    UInt8.ofBitVec ((BitVec.ofBoolListBE
      ((List.range 8).map fun offset => bits.getD (index * 8 + offset) false)).cast (by simp))).toArray⟩

@[simp] public theorem pack_size (bits : List Bool) : (pack bits).size = (bits.length + 7) / 8 := by
  simp [pack, ByteArray.size]

public theorem pack_bitSize (bits : List Bool) :
    bitSize (pack bits) ⟨bits.length % 8, Nat.mod_lt _ (by decide)⟩ = bits.length := by
  simp only [bitSize, pack_size]
  by_cases empty : bits.length = 0
  · simp [empty]
  · have nonempty : (bits.length + 7) / 8 ≠ 0 := by omega
    by_cases aligned : bits.length % 8 = 0
    · simp [nonempty, aligned]
      omega
    · simp [nonempty, aligned]
      omega

/-- Packing preserves every bit in transmission order. -/
@[simp] public theorem pack_toBits (bits : List Bool) :
    toBits (pack bits) ⟨bits.length % 8, Nat.mod_lt _ (by decide)⟩ = bits := by
  simp only [toBits, pack_bitSize]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have byteValid : i / 8 < (pack bits).size := by rw [pack_size]; omega
    have offset : i % 8 < 8 := Nat.mod_lt _ (by decide)
    have position : i / 8 * 8 + i % 8 = i := by omega
    simp only [List.getElem_map, List.getElem_range]
    rw [getElem!_pos (pack bits) (i / 8) byteValid]
    simp [ByteArray.getElem_eq_getElem_data, pack, offset, position, List.getElem?_eq_getElem hi']

end Lynx.Term.Bitstring
