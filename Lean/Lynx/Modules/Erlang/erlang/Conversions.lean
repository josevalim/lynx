module

public import Lynx.Pure

namespace Erlang.erlang
open Lynx

-- Only list elements may be bytes. A tail is itself iodata, so an integer
-- improper tail is rejected while a binary improper tail is accepted.
private def iodataBytes : Term → Option ByteArray
  | .nil => some ⟨#[]⟩
  | .bitstring bytes last _ => if last = 0 then some bytes else none
  | .cons head tail => do
    let first ← match head with
      | .integer byte =>
        if 0 ≤ byte ∧ byte ≤ 255 then some ⟨#[UInt8.ofNat byte.toNat]⟩ else none
      | _ => iodataBytes head
    let rest ← iodataBytes tail
    pure (first ++ rest)
  | _ => none

/-- Flatten nested byte lists and byte-aligned binaries. Binary tails are valid;
integer tails and unaligned bitstrings raise badarg. -/
#lynx_pure public def «iolist_to_binary/1» (value : Term) : Result :=
  match iodataBytes value with
  | some bytes => .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes))
  | none => .error (.error (.atom "badarg"))

/-- Decimal formatting of an arbitrary Erlang integer. -/
#lynx_pure @[expose] public def «integer_to_binary/1» : Term → Result
  | .integer value => .ok (.bitstring (toString value).toUTF8 0 (Term.Bitstring.valid_aligned _))
  | _ => .error (.error (.atom "badarg"))

public theorem iolist_to_binary_nil :
    «iolist_to_binary/1» .nil = .ok (.bitstring ⟨#[]⟩ 0 (Term.Bitstring.valid_aligned _)) := by
  simp [«iolist_to_binary/1», iodataBytes]

public theorem iolist_to_binary_binary (bytes : ByteArray) :
    «iolist_to_binary/1» (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes)) =
      .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes)) := by
  simp [«iolist_to_binary/1», iodataBytes]

/-- Nesting two valid iodata values preserves their concatenated byte sequence. -/
public theorem iolist_to_binary_join (left right : Term) (a b : ByteArray)
    (leftReturned : «iolist_to_binary/1» left = .ok (.bitstring a 0 (Term.Bitstring.valid_aligned a)))
    (rightReturned : «iolist_to_binary/1» right = .ok (.bitstring b 0 (Term.Bitstring.valid_aligned b))) :
    «iolist_to_binary/1» (.cons left right) =
      .ok (.bitstring (a ++ b) 0 (Term.Bitstring.valid_aligned _)) := by
  cases hl : iodataBytes left <;> simp [«iolist_to_binary/1», hl] at leftReturned
  cases hr : iodataBytes right <;> simp [«iolist_to_binary/1», hr] at rightReturned
  subst a b
  cases left <;> simp [iodataBytes] at hl <;>
    simp [«iolist_to_binary/1», iodataBytes, hl, hr]

/-- Adding a valid byte to an iolist prepends exactly that byte. -/
public theorem iolist_to_binary_byte_cons (byte : Int) (tail : Term) (bytes : ByteArray)
    (lower : 0 ≤ byte) (upper : byte ≤ 255)
    (returned : «iolist_to_binary/1» tail = .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes))) :
    «iolist_to_binary/1» (.cons (.integer byte) tail) =
      .ok (.bitstring (ByteArray.mk #[UInt8.ofNat byte.toNat] ++ bytes) 0 (Term.Bitstring.valid_aligned _)) := by
  cases ht : iodataBytes tail <;> simp [«iolist_to_binary/1», ht] at returned
  subst bytes
  simp [«iolist_to_binary/1», iodataBytes, lower, upper, ht]

end Erlang.erlang
