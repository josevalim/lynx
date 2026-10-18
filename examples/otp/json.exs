# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/json.exs
# Verify that OTP's json module decodes what it encodes.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
ExUnit.start()

defmodule JsonProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def roundtrip(data), do: :json.decode(:erlang.iolist_to_binary(:json.encode(data))) === data

  # The encoder escapes binaries with SWAR arithmetic on 56-bit words, whose
  # translation needs more than Lean's default elaboration budget.
  laws "json integer round trip", options: [maxHeartbeats: 0] do
    # Error reports format positions with functions outside the model.
    cutoff &:json.invalid_byte/2
    cutoff &:json.unexpected_sequence/2
    cutoff &:json.unexpected_utf8/2

    # The encoder writes integer_to_binary/1. The decoder dispatches on the first
    # byte, counts the digits, and reads the whole text back with
    # binary_to_integer/1, the integer decoder in its default options.
    law integer_roundtrip(n),
      requires: is_integer(n),
      expects: roundtrip(n),
      proof: ~LEAN"""
      open Lynx Lynx.Term.Bitstring Erlang.json in
      exact (by
        -- A leading digit other than zero starts a number of length one.
        have value_digit : ∀ (orig skip acc stack dec : Term) (b : UInt8) (bs : List UInt8),
            49 ≤ b.toNat → b.toNat ≤ 57 →
            «value/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer 1) := by
          intro orig skip acc stack dec b bs low high
          unfold «value/6»
          have h32 : (b.toNat : Int) ≠ 32 := by omega
          have h9 : (b.toNat : Int) ≠ 9 := by omega
          have h13 : (b.toNat : Int) ≠ 13 := by omega
          have h10 : (b.toNat : Int) ≠ 10 := by omega
          have h48 : (b.toNat : Int) ≠ 48 := by omega
          have digit : (b.toNat : Int) = 49 ∨ (b.toNat : Int) = 50 ∨ (b.toNat : Int) = 51 ∨
              (b.toNat : Int) = 52 ∨ (b.toNat : Int) = 53 ∨ (b.toNat : Int) = 54 ∨
              (b.toNat : Int) = 55 ∨ (b.toNat : Int) = 56 ∨ (b.toNat : Int) = 57 := by omega
          simp only [matchInteger_byte, Result.extract_some]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»,
            h32, h9, h13, h10, h48]
          rcases digit with h | h | h | h | h | h | h | h | h <;> simp [h]

        -- A minus sign is followed by a number.
        have value_minus : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((45 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
              stack dec =
              «number_minus/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, Result.extract_some]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- A leading zero starts a number that only continues with a fraction or exponent.
        have value_zero : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((48 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
              stack dec =
              «number_zero/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer 1) := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, Result.extract_some]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have number_minus_digit : ∀ (orig skip acc stack dec : Term) (b : UInt8) (bs : List UInt8),
            49 ≤ b.toNat → b.toNat ≤ 57 →
            «number_minus/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
              dec =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer 2) := by
          intro orig skip acc stack dec b bs low high
          have h48 : (b.toNat : Int) ≠ 48 := by omega
          have digit : (b.toNat : Int) = 49 ∨ (b.toNat : Int) = 50 ∨ (b.toNat : Int) = 51 ∨
              (b.toNat : Int) = 52 ∨ (b.toNat : Int) = 53 ∨ (b.toNat : Int) = 54 ∨
              (b.toNat : Int) = 55 ∨ (b.toNat : Int) = 56 ∨ (b.toNat : Int) = 57 := by omega
          unfold «number_minus/6»
          simp only [matchInteger_byte, Result.extract_some]
          simp [matchTail, Nat.mod_one, h48]
          rcases digit with h | h | h | h | h | h | h | h | h <;> simp [h]

        -- Each digit extends the number by one byte.
        have number_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
              (.integer len) =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte, Result.extract_some]
          have ge : (compare (b.toNat : Int) 48).isGE = true := by
            simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
          have le : (compare (b.toNat : Int) 57).isLE = true := by
            simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have number_digits : ∀ (orig skip acc stack dec : Term) (digits rest : List UInt8),
            (∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) → ∀ len : Int,
            «number/7» (.bitstring ⟨(digits ++ rest).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
              dec (.integer len) =
              «number/7» (.bitstring ⟨rest.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer (len + digits.length)) := by
          intro orig skip acc stack dec digits rest all len
          induction digits generalizing len with
          | nil => simp
          | cons d ds ih =>
            have bound := all d (by simp)
            simp only [List.cons_append]
            rw [number_digit orig skip acc stack dec len d (ds ++ rest) bound.1 bound.2,
              ih (fun x mem => all x (by simp [mem])) (len + 1)]
            have : len + 1 + (ds.length : Int) = len + ((d :: ds).length : Int) := by simp; omega
            rw [this]

        -- At the end of the input, the integer decoder reads the number's text.
        have number_end : ∀ (orig skip acc stack : Term) (len : Int),
            «number/7» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip acc
              stack (.tuple #[.atom "decode", .atom "undefined", .atom "undefined",
                .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined",
                .function 1 1 #[], .function 2 1 #[], .atom "undefined", .atom "null"])
              (.integer len) =
              (do
                let token ← Erlang.erlang.«binary_part/3» orig skip (.integer len)
                let value ← Term.apply (.function 2 1 #[]) #[token]
                «unexpected/8» orig skip acc stack (.tuple #[.atom "decode", .atom "undefined",
                    .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined",
                    .atom "undefined", .function 1 1 #[], .function 2 1 #[], .atom "undefined",
                    .atom "null"])
                  (.integer len) (.integer 0) (.tuple #[.atom "number", value])) := by
          intro orig skip acc stack len
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte_nil, Result.extract_none]
          simp

        have number_zero_end : ∀ (orig skip acc stack : Term) (len : Int),
            «number_zero/7» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip
              acc stack (.tuple #[.atom "decode", .atom "undefined", .atom "undefined",
                .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined",
                .function 1 1 #[], .function 2 1 #[], .atom "undefined", .atom "null"])
              (.integer len) =
              (do
                let value ← Term.apply (.function 2 1 #[]) #[.bitstring ⟨#[48]⟩ 0 (valid_aligned _)]
                «unexpected/8» orig skip acc stack (.tuple #[.atom "decode", .atom "undefined",
                    .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined",
                    .atom "undefined", .function 1 1 #[], .function 2 1 #[], .atom "undefined",
                    .atom "null"])
                  (.integer len) (.integer 0) (.tuple #[.atom "number", value])) := by
          intro orig skip acc stack len
          conv => lhs; unfold «number_zero/7»
          simp only [matchInteger_byte_nil, Result.extract_none]
          simp

        -- A number spanning the whole input is the complete result.
        have unexpected_whole : ∀ (bytes : ByteArray) (acc stack dec data : Term),
            «unexpected/8» (.bitstring bytes 0 (valid_aligned _)) (.integer 0) acc stack dec
              (.integer bytes.size) (.integer 0) data =
              .ok (.tuple #[.atom "continue",
                .tuple #[.bitstring bytes 0 (valid_aligned _), acc, stack, dec, data]]) := by
          intro bytes acc stack dec data
          unfold «unexpected/8»
          have rest : matchBinary (.bitstring bytes 0 (valid_aligned _)) (.integer 0) 8 =
              some (ofBits [], .bitstring bytes 0 (valid_aligned _)) := by
            simp [matchBinary, ofBits_toBits_aligned]
          have whole : matchTail (.bitstring bytes 0 (valid_aligned _)) (.atom "all") 8 = true := by
            simp only [matchTail, bitSize]
            split
            · split <;> simp
            · omega
          simp [Erlang.erlang.«byte_size/1», Erlang.erlang.«=</2», rest, whole]

        have decode_integer : ∀ (n : Int) (depth : Nat) (text : Term),
            Erlang.erlang.«integer_to_binary/1» (.integer n) = .ok text →
            Result.resolve Erlang.program.fun_table depth («decode/1» text) = .ok (.integer n) := by
          intro n depth text encoded
          have parsed := Erlang.erlang.binary_to_integer_integer_to_binary n
          rw [encoded] at parsed
          simp only [Result.ok_bind] at parsed
          obtain ⟨first, rest, decimal, digits, zero⟩ := Erlang.erlang.integer_to_binary_decimal n
          rw [encoded] at decimal
          cases decimal
          have size (l : List UInt8) : (ByteArray.mk l.toArray).size = l.length := by
            simp [ByteArray.size]
          have firstLow := (digits first (by simp)).1
          have firstHigh := (digits first (by simp)).2
          have restDigits : ∀ d ∈ rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57 :=
            fun d mem => digits d (by simp [mem])
          by_cases negative : n < 0
          · have firstPositive : 49 ≤ first.toNat := by
              have := digits first (by simp)
              by_cases eq : first.toNat = 48
              · have := (zero eq).1; omega
              · omega
            simp only [negative, if_true, List.cons_append, List.nil_append] at parsed ⊢
            unfold «decode/1»
            simp only []
            rw [value_minus, number_minus_digit _ _ _ _ _ first rest firstPositive firstHigh]
            have loop := number_digits
              (.bitstring ⟨((45 : UInt8) :: first :: rest).toArray⟩ 0 (valid_aligned _))
              (.integer 0) (.atom "ok") .nil
              (.tuple #[.atom "decode", .atom "undefined", .atom "undefined", .atom "undefined",
                .atom "undefined", .atom "undefined", .atom "undefined", .function 1 1 #[],
                .function 2 1 #[], .atom "undefined", .atom "null"]) rest [] restDigits 2
            simp only [List.append_nil] at loop
            rw [loop, number_end]
            have len : (2 + (rest.length : Int)) =
                ((ByteArray.mk ((45 : UInt8) :: first :: rest).toArray).size : Int) := by
              rw [size]; simp; omega
            rw [len]
            simp [Erlang.erlang.binary_part_whole, «$lynx_fun_2/1», parsed, unexpected_whole]
          · simp only [negative, if_false, List.nil_append] at parsed ⊢
            unfold «decode/1»
            simp only []
            by_cases leading : first.toNat = 48
            · obtain ⟨_, restNil⟩ := zero leading
              subst restNil
              have first48 : first = 48 := UInt8.toNat_inj.mp (by simpa using leading)
              subst first48
              rw [value_zero, number_zero_end]
              have len : (1 : Int) = ((ByteArray.mk ([(48 : UInt8)]).toArray).size : Int) := by
                rw [size]; simp
              rw [len]
              simp [«$lynx_fun_2/1», parsed, unexpected_whole]
            · rw [value_digit _ _ _ _ _ first rest (by omega) firstHigh]
              have loop := number_digits (.bitstring ⟨(first :: rest).toArray⟩ 0 (valid_aligned _))
                (.integer 0) (.atom "ok") .nil
                (.tuple #[.atom "decode", .atom "undefined", .atom "undefined", .atom "undefined",
                  .atom "undefined", .atom "undefined", .atom "undefined", .function 1 1 #[],
                  .function 2 1 #[], .atom "undefined", .atom "null"]) rest [] restDigits 1
              simp only [List.append_nil] at loop
              rw [loop, number_end]
              have len : (1 + (rest.length : Int)) =
                  ((ByteArray.mk (first :: rest).toArray).size : Int) := by
                rw [size]; simp; omega
              rw [len]
              simp [Erlang.erlang.binary_part_whole, «$lynx_fun_2/1», parsed, unexpected_whole]

        -- The encoder dispatches through the program table to integer_to_binary/1.
        have roundtrip_integer : ∀ n : Int,
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» (.integer n)) =
              .ok Term.true := by
          intro n
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          unfold «do_encode/2»
          simp only []
          obtain ⟨first, rest, text, -, -⟩ := Erlang.erlang.integer_to_binary_decimal n
          rw [text, Result.resolve_of_isPure _ _ _ (by simp)]
          simp only [Result.ok_bind, Result.resolve_bind, Erlang.erlang.iolist_to_binary_binary]
          rw [Result.resolve_of_isPure _ _ _ (by simp), Result.ok_bind,
            decode_integer n 100 _ text, Result.ok_bind, Result.resolve_of_isPure _ _ _ (by simp)]
          simp [Erlang.erlang.«=:=/2»]

        cases n <;> simp [«integer_roundtrip:requires/1», Erlang.erlang.«is_integer/1»] at requires
        rename_i n
        apply Lynx.run_of_resolve rfl
        simpa [«integer_roundtrip:ensures/1»] using roundtrip_integer n)
      """
  end
end
