module

public import Std

/-! Packed-bit operations exposed for reduction in proofs. -/

namespace Lynx.Term.Bitstring

/-- Packed storage is canonical: empty storage has no partial byte, and
unused low bits of the final byte are zero. -/
@[expose] public def Valid (bytes : ByteArray) (lastBits : Fin 8) : Prop :=
  (bytes.size = 0 → lastBits = 0) ∧
  (lastBits ≠ 0 → ∀ offset : Fin 8, lastBits.val ≤ offset.val →
    bytes[bytes.size - 1]!.toBitVec.getMsbD offset.val = false)

public instance (bytes : ByteArray) (lastBits : Fin 8) : Decidable (Valid bytes lastBits) := by
  unfold Valid
  infer_instance

@[simp] public theorem valid_aligned (bytes : ByteArray) : Valid bytes 0 := by
  simp [Valid]

/-- Number of meaningful bits. Zero means the last byte is fully used;
otherwise only its leading `lastBits` bits are used. Empty storage has zero
meaningful bits; `Term` requires its count to be zero and unused low bits
to be zero. -/
@[expose] public def bitSize (bytes : ByteArray) (lastBits : Fin 8) : Nat :=
  if bytes.size = 0 then 0
  else if lastBits = 0 then bytes.size * 8
  else (bytes.size - 1) * 8 + lastBits.val

namespace Measure

/-! Field measures used while deriving `SizeOf Term`. The default measures
follow byte values, which can grow when a match shifts bits. Here `bytes`
counts every byte as whole, and `lastBits` subtracts the unused bits of a
partial final byte. Both are offset by eight to stay in `Nat`, so a bitstring
measures its meaningful bits plus a constant, and matching a prefix decreases
`sizeOf`. -/

public scoped instance (priority := high) bytes : SizeOf ByteArray := ⟨fun bytes => 8 * bytes.size⟩
public scoped instance (priority := high) lastBits : SizeOf (Fin 8) :=
  ⟨fun lastBits => if lastBits = 0 then 8 else lastBits.val⟩

end Measure

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

/-- Decode transmission-order integer bits, with a possible partial final byte. -/
@[expose] public def decodeInteger (bits : List Bool) (little : Bool) : Nat :=
  if little then
    bits.zipIdx.foldl (fun value (bit, i) =>
      let shift := i / 8 * 8 + (min 8 (bits.length - i / 8 * 8) - 1 - i % 8)
      if bit then value + 2 ^ shift else value) 0
  else
    bits.foldl (fun value bit => value * 2 + if bit then 1 else 0) 0

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

/-- Packing establishes canonical storage for every bit sequence. -/
public theorem pack_valid (bits : List Bool) :
    Valid (pack bits) ⟨bits.length % 8, Nat.mod_lt _ (by decide)⟩ := by
  constructor
  · intro empty
    have size := pack_size bits
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  · intro unaligned offset unused
    change bits.length % 8 ≤ offset.val at unused
    have nonzero : bits.length % 8 ≠ 0 := by
      simpa only [ne_eq, Fin.ext_iff, Fin.val_zero] using unaligned
    have byteValid : (pack bits).size - 1 < (pack bits).size := by
      rw [pack_size]
      omega
    have beyond : bits.length ≤ ((pack bits).size - 1) * 8 + offset.val := by
      rw [pack_size]
      omega
    rw [getElem!_pos (pack bits) _ byteValid]
    simp [ByteArray.getElem_eq_getElem_data, pack, offset.isLt]
    change bits.getD (((pack bits).size - 1) * 8 + offset.val) false = false
    simp only [pack_size] at beyond ⊢
    simp only [List.getD, List.getElem?_eq_none beyond, Option.getD_none]

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

/-- Byte-aligned bit views cover exactly the stored bytes. -/
public theorem toBits_length_aligned (bytes : ByteArray) : (toBits bytes 0).length = bytes.size * 8 := by
  simp only [toBits, List.length_map, List.length_range, bitSize]
  split <;> simp_all

public theorem pack_toBits_aligned (bytes : ByteArray) : pack (toBits bytes 0) = bytes := by
  apply ByteArray.ext_getElem
  · rw [pack_size, toBits_length_aligned]
    omega
  · intro i hi hj
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getMsbD_eq
    intro offset ho
    have hpos : i * 8 + offset < (toBits bytes 0).length := by rw [toBits_length_aligned]; omega
    have bound : i < ((toBits bytes 0).length + 7) / 8 := by
      rw [←pack_size]
      exact hi
    simp only [ByteArray.getElem_eq_getElem_data, pack, List.getElem_toArray,
      List.getElem_map, List.getElem_range, UInt8.toBitVec_ofBitVec,
      BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE]
    simp only [List.getD, List.getElem?_map, (List.getElem?_range ho), Option.map_some,
      Option.getD_some]
    rw [List.getElem?_eq_getElem hpos]
    simp only [Option.getD_some, toBits, List.getElem_map, List.getElem_range]
    simp [getElem!_pos bytes i hj, ByteArray.getElem_eq_getElem_data,
      show (i * 8 + offset) / 8 = i by omega, show (i * 8 + offset) % 8 = offset by omega]

private theorem decode_acc (bits : List Bool) (acc : Nat) :
    bits.foldl (fun value bit => value * 2 + if bit then 1 else 0) acc =
      acc * 2 ^ bits.length + (BitVec.ofBoolListBE bits).toNat := by
  induction bits generalizing acc with
  | nil => simp [BitVec.ofBoolListBE]
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, BitVec.ofBoolListBE, BitVec.toNat_cons']
    cases b <;> simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.shiftLeft_eq]

private theorem decode_big (bits : List Bool) :
    decodeInteger bits false = (BitVec.ofBoolListBE bits).toNat := by
  simp [decodeInteger, decode_acc]

@[simp] public theorem integerBits_length (n : Int) (w : Nat) (little : Bool) :
    (integerBits n w little).length = w := by simp [integerBits]

/-- Unsigned big-endian encoding and decoding recover exactly the low bits. -/
public theorem decodeInteger_integerBits (n w : Nat) :
    decodeInteger (integerBits n w false) false = n % 2 ^ w := by
  rw [decode_big]
  have bits : (BitVec.ofBoolListBE (integerBits n w false)).cast (integerBits_length n w false) =
      BitVec.ofNat w n := by
    apply BitVec.eq_of_getMsbD_eq
    intro i
    simp only [BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE]
    by_cases hi : i < w
    · have hidx : w - 1 - i < w := by omega
      simp only [BitVec.getMsbD, BitVec.getLsbD, BitVec.toNat_ofNat,
        Nat.testBit_mod_two_pow, hi, hidx, decide_true, Bool.true_and]
      simp [integerBits, List.getD, hi, ← Int.natCast_shiftRight,
        Nat.testBit_eq_decide_div_mod_eq,
        Nat.shiftRight_eq_div_pow]
      have power : (2 : Int) ^ (w - 1 - i) = ((2 ^ (w - 1 - i) : Nat) : Int) := by simp
      rw [power, ← Int.natCast_ediv]
      change ((Int.ofNat (n / 2 ^ (w - 1 - i) % 2)) == Int.ofNat 1) = _
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    · simp [integerBits, List.getD, BitVec.getMsbD, hi]
  have := congrArg BitVec.toNat bits
  simpa using this

/-- Split a big-endian integer into independently decodable fields. -/
public theorem integerBits_add (n : Int) (left right : Nat) :
    integerBits n (left + right) false =
      integerBits (n >>> right) left false ++ integerBits n right false := by
  simp only [integerBits, Bool.false_eq_true, ↓reduceIte, List.range_add, List.map_append,
    List.map_map, Function.comp_def]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi : i < left := List.mem_range.mp hi
    rw [← Int.shiftRight_add]
    have shift : right + (left - 1 - i) = left + right - 1 - i := by omega
    rw [shift]
  · apply List.map_congr_left
    intro i hi
    have shift : left + right - 1 - (left + i) = right - 1 - i := by omega
    rw [shift]


/-- An unsigned field fits in its transmission width. -/
public theorem decodeInteger_lt (bits : List Bool) :
    decodeInteger bits false < 2 ^ bits.length := by
  rw [decode_big]
  exact (BitVec.ofBoolListBE bits).isLt

/-- Decoding and re-encoding a big-endian field preserves every input bit. -/
public theorem integerBits_decodeInteger (bits : List Bool) :
    integerBits (decodeInteger bits false) bits.length false = bits := by
  have bound := decodeInteger_lt bits
  have returned := decodeInteger_integerBits (decodeInteger bits false) bits.length
  rw [Nat.mod_eq_of_lt bound] at returned
  have vectors :
      (BitVec.ofBoolListBE (integerBits (decodeInteger bits false) bits.length false)).cast
        (integerBits_length _ _ _) = BitVec.ofBoolListBE bits := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_cast, ←decode_big] using returned
  apply List.ext_getElem
  · exact integerBits_length _ _ _
  · intro index leftBound rightBound
    have field := congrArg (fun value : BitVec bits.length => value.getMsbD index) vectors
    simpa only [BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE, List.getD,
      List.getElem?_eq_getElem leftBound, List.getElem?_eq_getElem rightBound,
      Option.getD_some] using field

end Lynx.Term.Bitstring
