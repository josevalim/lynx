module

public import Lynx.Term

public section

/-! Portable term hashing, following `make_hash2` in OTP's `erl_term_hashing.c`.

Hashes of integers, floats, atoms, bitstrings, lists, tuples, and maps match
the BEAM on 64-bit platforms. The BEAM hashes PIDs, references, and functions
by runtime identifiers that Lynx does not model, so their hashes are
unspecified: proofs may only rely on them being deterministic and in range. -/

namespace Erlang.erlang

open Lynx

/-- Bob Jenkins' mixing function, as `MIX` in OTP. -/
private def mix (a b c : UInt32) : UInt32 × UInt32 × UInt32 :=
  let a := a - b - c
  let a := a ^^^ (c >>> 13)
  let b := b - c - a
  let b := b ^^^ (a <<< 8)
  let c := c - a - b
  let c := c ^^^ (b >>> 13)
  let a := a - b - c
  let a := a ^^^ (c >>> 12)
  let b := b - c - a
  let b := b ^^^ (a <<< 16)
  let c := c - a - b
  let c := c ^^^ (b >>> 5)
  let a := a - b - c
  let a := a ^^^ (c >>> 3)
  let b := b - c - a
  let b := b ^^^ (a <<< 10)
  let c := c - a - b
  let c := c ^^^ (b >>> 15)
  (a, b, c)

/-- `HCONST * n`, the golden ratio multiples OTP uses to separate term kinds. -/
private def hconst (n : UInt32) : UInt32 := 0x9e3779b9 * n

/-- `UINT32_HASH_2`, mixing two words into the running hash. -/
private def hashWords (x y constant hash : UInt32) : UInt32 :=
  (mix (constant + x) (constant + y) hash).2.2

/-- `UINT32_HASH`. -/
private def hashWord (x constant hash : UInt32) : UInt32 :=
  hashWords x 0 constant hash

private def wrap (value : Int) : UInt32 := UInt32.ofNat (value % 2 ^ 32).toNat

/-- Integers in `[-2^27, 2^27)` are mixed as signed words; negative ones twice.
Larger magnitudes are mixed in 64-bit digits, least significant first, which
matches both large immediates and bignums. -/
private def hashInteger (value : Int) (hash : UInt32) : UInt32 :=
  if -2 ^ 27 ≤ value ∧ value < 2 ^ 27 then
    let hash := if value < 0 then hashWord (wrap (-value)) (hconst 1) hash else hash
    hashWord (wrap value) (hconst 1) hash
  else
    let constant := if value < 0 then hconst 10 else hconst 11
    let rec digits (magnitude : Nat) (hash : UInt32) : UInt32 :=
      let hash := hashWords (UInt32.ofNat magnitude) (UInt32.ofNat (magnitude / 2 ^ 32))
        constant hash
      if magnitude < 2 ^ 64 then hash else digits (magnitude / 2 ^ 64) hash
    termination_by magnitude
    decreasing_by omega
    digits value.natAbs hash

/-- The positive zero replaces negative zero before mixing the IEEE words. -/
private def hashFloat (value : Term.FiniteFloat) (hash : UInt32) : UInt32 :=
  let bits :=
    if value.exponent.val = 0 ∧ value.fraction.val = 0 then 0
    else (if value.negative then 2 ^ 63 else 0) + value.exponent.val * 2 ^ 52 + value.fraction.val
  hashWords (UInt32.ofNat (bits / 2 ^ 32)) (UInt32.ofNat bits) (hconst 12) hash

/-- The atom table's hashpjw over the UTF-8 name, in a 64-bit word. Two-byte
sequences for Latin-1 characters are folded into their code point. -/
private def atomTableHash (name : String) : UInt32 :=
  let step (h : UInt64) (v : UInt8) : UInt64 :=
    let h := (h <<< 4) + v.toUInt64
    let g := h &&& 0xf0000000
    if g = 0 then h else h ^^^ (g >>> 24) ^^^ g
  let rec go (h : UInt64) : List UInt8 → UInt64
    | [] => h
    | v :: next :: rest =>
      if v &&& 0xFE = 0xC2 ∧ next &&& 0xC0 = 0x80 then go (step h ((v <<< 6) ||| (next &&& 0x3F))) rest
      else go (step h v) (next :: rest)
    | [v] => step h v
  (go 0 name.toUTF8.toList).toUInt32

/-- The leading atom or `[]` of a hash takes its table value without mixing. -/
private def hashAtom (name : String) (hash : UInt32) : UInt32 :=
  if hash = 0 then atomTableHash name else hashWord (atomTableHash name) (hconst 3) hash

private def hashNil (hash : UInt32) : UInt32 :=
  if hash = 0 then 3468870702 else hashWord 2 (hconst 2) hash

private def word (bytes : ByteArray) (offset : Nat) : UInt32 :=
  bytes[offset]!.toUInt32 ||| (bytes[offset + 1]!.toUInt32 <<< 8) |||
    (bytes[offset + 2]!.toUInt32 <<< 16) ||| (bytes[offset + 3]!.toUInt32 <<< 24)

/-- Jenkins' lookup2 over the first `length` bytes, as `block_hash` in OTP. -/
private def blockHash (bytes : ByteArray) (length : Nat) (initial : UInt32) : UInt32 :=
  let rec blocks (offset : Nat) (a b c : UInt32) : UInt32 :=
    if offset + 12 ≤ length then
      let (a, b, c) := mix (a + word bytes offset) (b + word bytes (offset + 4))
        (c + word bytes (offset + 8))
      blocks (offset + 12) a b c
    else
      let byte (index : Nat) (shift : UInt32) : UInt32 :=
        if offset + index < length then bytes[offset + index]!.toUInt32 <<< shift else 0
      let a := a + byte 0 0 + byte 1 8 + byte 2 16 + byte 3 24
      let b := b + byte 4 0 + byte 5 8 + byte 6 16 + byte 7 24
      -- The first byte of `c` is reserved for the length.
      let c := c + UInt32.ofNat length + byte 8 8 + byte 9 16 + byte 10 24
      (mix a b c).2.2
  termination_by length - offset
  blocks 0 0x9e3779b9 0x9e3779b9 initial

/-- Whole bytes go through the block hash, then any trailing bits with their count. -/
private def hashBitstring (bytes : ByteArray) (lastBits : Fin 8) (hash : UInt32) : UInt32 :=
  let whole := if lastBits = 0 then bytes.size else bytes.size - 1
  let constant := hconst 13 + hash
  if bytes.size = 0 then constant
  else
    let hash := blockHash bytes whole constant
    if lastBits = 0 then hash
    else hashWords lastBits.val.toUInt32 (bytes[whole]! >>> (8 - lastBits.val.toUInt8)).toUInt32
      (hconst 15) hash

/-- Runtime identities the BEAM hashes but Lynx does not model. -/
private opaque hashIdentity (term : Term) (hash : UInt32) : UInt32

private def byte? : Term → Option UInt32
  | .integer value => if 0 ≤ value ∧ value < 256 then some (wrap value) else none
  | _ => none

/-- Erlang term equality on map keys, deciding which bindings are visible. -/
private def sameKey (a b : Term) : Bool := Term.exactCompare a b == .eq

private theorem sizeOf_pos (term : Term) : 0 < sizeOf term := by
  cases term <;> simp <;> omega

mutual

/-- Hash a term into the running hash, in `make_hash2`'s traversal order. -/
private def hashTerm (hash : UInt32) : Term → UInt32
  | .integer value => hashInteger value hash
  | .float value => hashFloat value hash
  | .atom name => hashAtom name hash
  | .nil => hashNil hash
  | .cons head tail => hashList hash 0 0 head tail
  | .tuple elements =>
    elements.attach.foldl (fun hash element => hashTerm hash element.val)
      (hashWord (UInt32.ofNat elements.size) (hconst 9) hash)
  | .map entries =>
    let (size, pairs) := hashPairs [] entries
    let hash := hashWord (UInt32.ofNat size) (hconst 16) hash
    if size = 0 then hash else hashWord pairs (hconst 19) hash
  | .bitstring bytes lastBits _ => hashBitstring bytes lastBits hash
  | term@(.pid _) | term@(.reference _) | term@(.function ..) => hashIdentity term hash
termination_by term => sizeOf term
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem element.property; simp_all; try omega)
    | (simp_all; try omega)

/-- Byte elements are packed four at a time, as strings are. The run ends at
an improper tail, which is hashed next, or at another element, which is hashed
before the rest of the list. -/
private def hashList (hash packed : UInt32) (count : Nat) (head tail : Term) : UInt32 :=
  let flush (hash : UInt32) := if count > 0 then hashWord packed (hconst 4) hash else hash
  match byte? head with
  | some value =>
    let packed := (packed <<< 8) + value
    let (hash, packed, count) :=
      if count = 3 then (hashWord packed (hconst 4) hash, 0, 0) else (hash, packed, count + 1)
    match tail with
    | .cons head tail => hashList hash packed count head tail
    | tail => hashTerm (if count > 0 then hashWord packed (hconst 4) hash else hash) tail
  | none => hashTerm (hashTerm (flush hash) head) tail
termination_by sizeOf head + sizeOf tail
decreasing_by all_goals (have := sizeOf_pos head; have := sizeOf_pos tail; simp_all; try omega)

/-- The number of visible bindings and the XOR of their independent hashes. -/
private def hashPairs (seen : List Term) : List (Term × Term) → Nat × UInt32
  | [] => (0, 0)
  | (key, value) :: rest =>
    let (size, pairs) := hashPairs (if seen.any (sameKey key) then seen else key :: seen) rest
    if seen.any (sameKey key) then (size, pairs)
    else (size + 1, pairs ^^^ hashTerm (hashTerm 0 key) value)
termination_by entries => sizeOf entries

end

/-- The full 32-bit portable hash of a term. -/
private def hash2 (term : Term) : UInt32 := hashTerm 0 term

/-- `erlang:phash2/1`: the portable hash in `[0, 2^27)`. -/
def «phash2/1» (term : Term) : Except Exception Term :=
  .ok (.integer (hash2 term &&& (2 ^ 27 - 1)).toNat)

/-- `erlang:phash2/2`: the portable hash in `[0, Range)`, for `Range` in `[1, 2^32]`. -/
def «phash2/2» (term range : Term) : Except Exception Term :=
  match range with
  | .integer (.ofNat (n + 1)) =>
    if n + 1 ≤ 2 ^ 32 then .ok (.integer ((hash2 term).toNat % (n + 1))) else .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- `phash2/1` always returns an integer in `[0, 2^27)`. -/
theorem phash2_range (term : Term) :
    ∃ hash : Nat, «phash2/1» term = .ok (.integer hash) ∧ hash < 2 ^ 27 :=
  ⟨_, rfl, Nat.lt_of_le_of_lt (by simpa using Nat.and_le_right) (by decide)⟩

end Erlang.erlang
