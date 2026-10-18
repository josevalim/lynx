# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/json.exs
# Verify that OTP's json module decodes what it encodes.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
ExUnit.start()

defmodule JsonProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  # Checking the translated json module alone takes about a minute.
  @moduletag timeout: to_timeout(minute: 5)

  def roundtrip(data), do: :json.decode(:erlang.iolist_to_binary(:json.encode(data))) === data

  # The data covered so far: integers and lists of integers.
  def supported?(data) when is_integer(data), do: true
  def supported?(data) when is_list(data), do: integers?(data)
  def supported?(_data), do: false

  def integers?([]), do: true
  def integers?([x | xs]), do: is_integer(x) and integers?(xs)
  def integers?(_), do: false

  # The encoder escapes binaries with SWAR arithmetic on 56-bit words, whose
  # translation needs more than Lean's default elaboration budget.
  laws "json round trip", options: [maxHeartbeats: 0] do
    # Error reports format positions with functions outside the model.
    cutoff &:json.invalid_byte/2
    cutoff &:json.unexpected_sequence/2
    cutoff &:json.unexpected_utf8/2

    prelude ~LEAN"""
    namespace JsonProof
    open Lynx

    /-- The options record `json:decode/1` passes to the decoder. -/
    abbrev options : Term := .tuple #[.atom "decode", .atom "undefined", .atom "undefined",
      .atom "undefined", .atom "undefined", .atom "undefined", .atom "undefined", .function 1 1
          #[],
      .function 2 1 #[], .atom "undefined", .atom "null"]

    /-- An Erlang list of integers. -/
    @[expose] def ints : List Int → Term
      | [] => .nil
      | x :: xs => .cons (.integer x) (ints xs)

    /-- The decimal text `integer_to_binary/1` writes for an integer. -/
    @[expose] def textOf (x : Int) : List UInt8 := (toString x).toUTF8.data.toList

    /-- The text after a list's first element: a comma before each element, then `]`. -/
    @[expose] def tailText : List Int → List UInt8
      | [] => [93]
      | y :: ys => 44 :: (textOf y ++ tailText ys)

    /-- The text the encoder writes for a list of integers. -/
    @[expose] def listText : List Int → List UInt8
      | [] => [91, 93]
      | x :: xs => 91 :: (textOf x ++ tailText xs)

    /-- The iodata `list_loop/2` builds for the elements after the first. -/
    @[expose] def loopIodata : List Int → Term
      | [] => .cons (.integer 93) .nil
      | y :: ys => .cons (.integer 44)
        (.cons (.bitstring ⟨(textOf y).toArray⟩ 0 (Term.Bitstring.valid_aligned _)) (loopIodata
            ys))

    end JsonProof
    """

    # The encoder writes integers with integer_to_binary/1 and lists as their
    # elements between brackets, separated by commas. The decoder dispatches on
    # each byte, reads integers back with binary_to_integer/1, the integer
    # decoder in its default options, and pushes them onto an array frame.
    law json_roundtrip(data),
      requires: supported?(data),
      expects: roundtrip(data),
      proof: ~LEAN"""
      open Lynx Lynx.Term.Bitstring Erlang.json JsonProof in
      exact (by
        -- A leading digit other than zero starts a number of length one.
        have value_digit : ∀ (orig skip acc stack dec : Term) (b : UInt8) (bs : List UInt8),
            49 ≤ b.toNat → b.toNat ≤ 57 →
            «value/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                dec =
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
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»,
            h32, h9, h13, h10, h48]
          rcases digit with h | h | h | h | h | h | h | h | h <;> simp [h]

        -- A minus sign is followed by a number.
        have value_minus : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((45 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc
              stack dec =
              «number_minus/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                  dec := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- A leading zero starts a number that only continues with a fraction or exponent.
        have value_zero : ∀ (orig skip acc stack dec : Term) (bs : List UInt8),
            «value/6» (.bitstring ⟨((48 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc
              stack dec =
              «number_zero/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                  dec
                (.integer 1) := by
          intro orig skip acc stack dec bs
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have number_minus_digit : ∀ (orig skip acc stack dec : Term) (b : UInt8) (bs : List
            UInt8),
            49 ≤ b.toNat → b.toNat ≤ 57 →
            «number_minus/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack
              dec =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer 2) := by
          intro orig skip acc stack dec b bs low high
          have h48 : (b.toNat : Int) ≠ 48 := by omega
          have digit : (b.toNat : Int) = 49 ∨ (b.toNat : Int) = 50 ∨ (b.toNat : Int) = 51 ∨
              (b.toNat : Int) = 52 ∨ (b.toNat : Int) = 53 ∨ (b.toNat : Int) = 54 ∨
              (b.toNat : Int) = 55 ∨ (b.toNat : Int) = 56 ∨ (b.toNat : Int) = 57 := by omega
          unfold «number_minus/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, h48]
          rcases digit with h | h | h | h | h | h | h | h | h <;> simp [h]

        -- Each digit extends the number by one byte.
        have number_digit : ∀ (orig skip acc stack dec : Term) (len : Int) (b : UInt8)
            (bs : List UInt8), 48 ≤ b.toNat → b.toNat ≤ 57 →
            «number/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                dec
              (.integer len) =
              «number/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack dec
                (.integer (len + 1)) := by
          intro orig skip acc stack dec len b bs low high
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          have ge : (compare (b.toNat : Int) 48).isGE = true := by
            simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
          have le : (compare (b.toNat : Int) 57).isLE = true := by
            simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
          simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2», ge, le]

        have number_digits : ∀ (orig skip acc stack dec : Term) (digits rest : List UInt8),
            (∀ d ∈ digits, 48 ≤ d.toNat ∧ d.toNat ≤ 57) → ∀ len : Int,
            «number/7» (.bitstring ⟨(digits ++ rest).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack
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
              stack options
              (.integer len) =
              (do
                let token ← Erlang.erlang.«binary_part/3» orig skip (.integer len)
                let value ← Term.apply (.function 2 1 #[]) #[token]
                «unexpected/8» orig skip acc stack options
                  (.integer len) (.integer 0) (.tuple #[.atom "number", value])) := by
          intro orig skip acc stack len
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte_nil, extract_none, matchEnd_byte_nil]
          simp

        have number_zero_end : ∀ (orig skip acc stack : Term) (len : Int),
            «number_zero/7» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip
              acc stack options
              (.integer len) =
              (do
                let value ← Term.apply (.function 2 1 #[]) #[.bitstring ⟨#[48]⟩ 0 (valid_aligned
                    _)]
                «unexpected/8» orig skip acc stack options
                  (.integer len) (.integer 0) (.tuple #[.atom "number", value])) := by
          intro orig skip acc stack len
          conv => lhs; unfold «number_zero/7»
          simp only [matchInteger_byte_nil, extract_none, matchEnd_byte_nil]
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
          have whole : matchTail (.bitstring bytes 0 (valid_aligned _)) (.atom "all") 8 = true :=
              by
            simp only [matchTail, bitSize]
            split
            · split <;> simp
            · omega
          simp [Erlang.erlang.«byte_size/1», Erlang.erlang.«=</2», rest, whole]

        have decode_integer : ∀ (n : Int) (depth : Nat) (text : Term),
            Erlang.erlang.«integer_to_binary/1» (.integer n) = .ok text →
            Result.resolve Erlang.program.fun_table depth («decode/1» text) = .ok (.integer n) :=
                by
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
              options rest [] restDigits 2
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
              have loop := number_digits (.bitstring ⟨(first :: rest).toArray⟩ 0 (valid_aligned
                  _))
                (.integer 0) (.atom "ok") .nil
                options rest [] restDigits 1
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

        have continue_array : ∀ (bs : List UInt8) (orig skip acc rest value : Term),
            «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc (.cons
                (.atom "array") rest) options value =
              «array_push/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc (.cons
                  (.atom "array") rest) options value := by
          intro bs orig skip acc rest value
          conv => lhs; unfold «continue/7»
          simp [matchTail, Nat.mod_one]

        have continue_top : ∀ (bs : List UInt8) (orig skip acc value : Term),
            «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc .nil options
                value =
              «terminate/5» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc value :=
                  by
          intro bs orig skip acc value
          conv => lhs; unfold «continue/7»
          simp [matchTail, Nat.mod_one]

        have terminate_end : ∀ (orig skip acc value : Term),
            «terminate/5» (.bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)) orig skip
                acc value =
              .ok (.tuple #[value, acc, .bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned
                  _)]) := by
          intro orig skip acc value
          unfold «terminate/5»
          simp [matchInteger_byte_nil, matchEnd_byte_nil]

        have array_push_comma : ∀ (bs : List UInt8) (orig skip acc stack value : Term),
            «array_push/7» (.bitstring ⟨((44 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig
                skip acc stack options value =
              (do
                let next ← Erlang.erlang.«+/2» skip (.integer 1)
                «value/6» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig next (.cons value
                    acc) stack options) := by
          intro bs orig skip acc stack value
          conv => lhs; unfold «array_push/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have array_push_close : ∀ (bs : List UInt8) (orig skip acc old stack value : Term),
            «array_push/7» (.bitstring ⟨((93 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig
                skip acc
                (.cons (.atom "array") (.cons old stack)) options value =
              (do
                let list ← Erlang.lists.«reverse/1» (.cons value acc)
                let next ← Erlang.erlang.«+/2» skip (.integer 1)
                «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig next old stack
                    options list) := by
          intro bs orig skip acc old stack value
          conv => lhs; unfold «array_push/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have value_open : ∀ (bs : List UInt8) (orig skip acc stack : Term),
            «value/6» (.bitstring ⟨((91 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig skip
                acc stack options =
              «array_start/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                  options (.integer 1) := by
          intro bs orig skip acc stack
          unfold «value/6»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        -- An array whose first element starts with a minus sign or a digit.
        have array_start_value : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term)
            (len : Int) (start : b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57)),
            «array_start/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack options (.integer len) =
              (do
                let next ← Erlang.erlang.«+/2» skip (.integer len)
                «value/6» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig next .nil
                  (.cons (.atom "array") (.cons acc stack)) options) := by
          intro b bs orig skip acc stack len start
          have h32 : (b.toNat : Int) ≠ 32 := by omega
          have h9 : (b.toNat : Int) ≠ 9 := by omega
          have h13 : (b.toNat : Int) ≠ 13 := by omega
          have h10 : (b.toNat : Int) ≠ 10 := by omega
          have h93 : (b.toNat : Int) ≠ 93 := by omega
          conv => lhs; unfold «array_start/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», h32, h9,
            h13, h10, h93]

        -- A number stops at a separator, reading its text with the integer decoder.
        have number_stop : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term) (len :
            Int) (separator : b.toNat = 44 ∨ b.toNat = 93),
            «number/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc stack
                options (.integer len) =
              (do
                let token ← Erlang.erlang.«binary_part/3» orig skip (.integer len)
                let value ← Term.apply (.function 2 1 #[]) #[token]
                let next ← Erlang.erlang.«+/2» skip (.integer len)
                «continue/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig next acc
                    stack options value) := by
          intro b bs orig skip acc stack len separator
          have h46 : (b.toNat : Int) ≠ 46 := by omega
          have h69 : (b.toNat : Int) ≠ 69 := by omega
          have h101 : (b.toNat : Int) ≠ 101 := by omega
          conv => lhs; unfold «number/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          rcases separator with h | h
          · have ge : ¬ (compare (b.toNat : Int) 48).isGE = true := by
              simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
            simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
              Erlang.erlang.«=:=/2»,
              Erlang.erlang.«or/2», ge, h46, h69, h101]
          · have ge : (compare (b.toNat : Int) 48).isGE = true := by
              simp [Ordering.isGE_iff_ne_lt, Int.compare_eq_lt]; omega
            have le : ¬ (compare (b.toNat : Int) 57).isLE = true := by
              simp [Ordering.isLE_iff_ne_gt, Int.compare_eq_gt]; omega
            simp [matchTail, Nat.mod_one, Erlang.erlang.«>=/2», Erlang.erlang.«=</2»,
              Erlang.erlang.«=:=/2»,
              Erlang.erlang.«or/2», ge, le, h46, h69, h101]

        have number_zero_stop : ∀ (b : UInt8) (bs : List UInt8) (orig skip acc stack : Term) (len
            : Int) (separator : b.toNat = 44 ∨ b.toNat = 93),
            «number_zero/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig skip acc
                stack options (.integer len) =
              (do
                let value ← Term.apply (.function 2 1 #[]) #[.bitstring ⟨#[48]⟩ 0 (valid_aligned
                    _)]
                let next ← Erlang.erlang.«+/2» skip (.integer len)
                «continue/7» (.bitstring ⟨(b :: bs).toArray⟩ 0 (valid_aligned _)) orig next acc
                    stack options value) := by
          intro b bs orig skip acc stack len separator
          have h46 : (b.toNat : Int) ≠ 46 := by omega
          have h69 : (b.toNat : Int) ≠ 69 := by omega
          have h101 : (b.toNat : Int) ≠ 101 := by omega
          conv => lhs; unfold «number_zero/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2», h46, h69,
            h101]

        have binary_part_middle : ∀ (pre mid post : List UInt8),
            Erlang.erlang.«binary_part/3» (.bitstring ⟨(pre ++ mid ++ post).toArray⟩ 0
                (valid_aligned _))
                (.integer pre.length) (.integer mid.length) =
              .ok (.bitstring ⟨mid.toArray⟩ 0 (valid_aligned _)) := by
          intro pre mid post
          have size : (ByteArray.mk (pre ++ mid ++ post).toArray).size = pre.length + mid.length
              + post.length := by
            simp [ByteArray.size]; omega
          have nonneg : ¬ ((mid.length : Int) < 0) := by omega
          simp only [Erlang.erlang.«binary_part/3», nonneg, if_false, size]
          have bounds : (0 : Int) ≤ pre.length ∧ (pre.length : Int) ≤ pre.length + mid.length ∧
              (pre.length + mid.length : Int) ≤ ((pre.length + mid.length + post.length : Nat) :
                  Int) := by omega
          simp only [bounds, and_self, if_true]
          congr 2
          apply ByteArray.ext
          rw [ByteArray.data_extract]
          have : ((pre.length : Int) + mid.length).toNat - pre.length = mid.length := by omega
          simp [this]

        have decode_element : ∀ (x : Int) (pre post : List UInt8) (b : UInt8) (separator :
            b.toNat = 44 ∨ b.toNat = 93) (acc stack : Term) (depth : Nat) (first : UInt8) (rest :
            List UInt8) (encoded : Erlang.erlang.«integer_to_binary/1» (.integer x) = .ok
            (.bitstring ⟨((if x < 0 then [45] else []) ++ first :: rest).toArray⟩ 0
            (valid_aligned _))) (digits : ∀ d ∈ first :: rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57) (zero
            : first.toNat = 48 → x = 0 ∧ rest = []),
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(((if x < 0 then [45] else []) ++ first :: rest) ++ b ::
                    post).toArray⟩ 0
                    (valid_aligned _))
                  (.bitstring ⟨(pre ++ ((if x < 0 then [45] else []) ++ first :: rest) ++ b ::
                      post).toArray⟩ 0
                    (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨(b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ ((if x < 0 then [45] else []) ++ first :: rest) ++ b ::
                      post).toArray⟩ 0
                    (valid_aligned _))
                  (.integer (pre.length + ((if x < 0 then [45] else []) ++ first ::
                      rest).length)) acc stack options
                  (.integer x)) := by
          intro x pre post b separator acc stack depth first rest encoded digits zero
          have parsed := Erlang.erlang.binary_to_integer_integer_to_binary x
          rw [encoded] at parsed
          simp only [Result.ok_bind] at parsed
          have firstLow := (digits first (by simp)).1
          have firstHigh := (digits first (by simp)).2
          have restDigits : ∀ d ∈ rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57 := fun d mem => digits d (by
              simp [mem])
          by_cases negative : x < 0
          · have firstPositive : 49 ≤ first.toNat := by
              by_cases eq : first.toNat = 48
              · have := (zero eq).1; omega
              · omega
            simp only [negative, if_true, List.cons_append, List.nil_append] at parsed ⊢
            rw [value_minus,
              number_minus_digit _ _ _ _ _ first (rest ++ b :: post) firstPositive firstHigh,
              number_digits _ _ _ _ _ rest (b :: post) restDigits 2, number_stop b post _ _ _ _ _
                  separator]
            have part := binary_part_middle pre ((45 : UInt8) :: first :: rest) (b :: post)
            simp only [List.length_cons] at part ⊢
            have len : (2 + (rest.length : Int)) = ((rest.length + 1 + 1 : Nat) : Int) := by omega
            rw [len, part]
            simp [«$lynx_fun_2/1», parsed]
          · simp only [negative, if_false, List.nil_append] at parsed ⊢
            by_cases leading : first.toNat = 48
            · obtain ⟨_, restNil⟩ := zero leading
              subst restNil
              have first48 : first = 48 := UInt8.toNat_inj.mp (by simpa using leading)
              subst first48
              simp only [List.cons_append, List.nil_append]
              rw [value_zero, number_zero_stop b post _ _ _ _ _ separator]
              simp [«$lynx_fun_2/1», parsed]
            · simp only [List.cons_append]
              rw [value_digit _ _ _ _ _ first (rest ++ b :: post) (by omega) firstHigh,
                number_digits _ _ _ _ _ rest (b :: post) restDigits 1, number_stop b post _ _ _ _
                    _ separator]
              have part := binary_part_middle pre (first :: rest) (b :: post)
              simp only [List.length_cons] at part ⊢
              have len : (1 + (rest.length : Int)) = ((rest.length + 1 : Nat) : Int) := by omega
              rw [len, part]
              simp [«$lynx_fun_2/1», parsed]

        have reverse2_ints : ∀ (l tail : List Int),
            Erlang.lists.«reverse/2» (ints l) (ints tail) = .ok (ints (l.reverse ++ tail)) := by
          intro l tail
          induction l generalizing tail with
          | nil => simp [ints, Erlang.lists.«reverse/2»]
          | cons x xs ih =>
            simp only [ints, Erlang.lists.«reverse/2»]
            rw [show Term.cons (.integer x) (ints tail) = ints (x :: tail) from rfl, ih]
            simp

        have reverse1_ints : ∀ (l : List Int),
            Erlang.lists.«reverse/1» (ints l) = .ok (ints l.reverse) := by
          intro l
          match l with
          | [] => simp [ints, Erlang.lists.«reverse/1»]
          | [a] => simp [ints, Erlang.lists.«reverse/1»]
          | [a, b] => simp [ints, Erlang.lists.«reverse/1»]
          | a :: b :: c :: rest =>
            unfold Erlang.lists.«reverse/1»
            simp only [ints]
            rw [show Term.list [.integer b, .integer a] = ints [b, a] from rfl,
              show Term.cons (.integer c) (ints rest) = ints (c :: rest) from rfl, reverse2_ints]
            simp

        have textOf_decimal : ∀ (x : Int),
            ∃ (first : UInt8) (rest : List UInt8),
              textOf x = (if x < 0 then [45] else []) ++ first :: rest ∧
              Erlang.erlang.«integer_to_binary/1» (.integer x) =
                .ok (.bitstring ⟨((if x < 0 then [45] else []) ++ first :: rest).toArray⟩ 0
                    (valid_aligned _)) ∧
              (∀ d ∈ first :: rest, 48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧ (first.toNat = 48 → x = 0 ∧
                  rest = []) := by
          intro x
          obtain ⟨first, rest, encoded, digits, zero⟩ := Erlang.erlang.integer_to_binary_decimal x
          refine ⟨first, rest, ?_, encoded, digits, zero⟩
          simp only [Erlang.erlang.«integer_to_binary/1», Result.ok.injEq,
            Term.bitstring.injEq] at encoded
          rw [textOf, encoded.1]

        -- A number embedded in the input, followed by a separator, continues with its value.
        have element : ∀ (x : Int) (pre post : List UInt8) (b : UInt8) (separator : b.toNat = 44
            ∨ b.toNat = 93) (acc stack : Term) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(textOf x ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ textOf x ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) acc stack options) =
              Result.resolve Erlang.program.fun_table depth
                («continue/7» (.bitstring ⟨(b :: post).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ textOf x ++ b :: post).toArray⟩ 0 (valid_aligned _))
                  (.integer (pre.length + (textOf x).length)) acc stack options (.integer x)) :=
                      by
          intro x pre post b separator acc stack depth
          obtain ⟨first, rest, text, encoded, digits, zero⟩ := textOf_decimal x
          rw [text]
          exact decode_element x pre post b separator acc stack depth first rest encoded digits zero

        have loop : ∀ (xs : List Int),
            ∀ (x : Int) (pre : List UInt8) (done : List Int) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («value/6» (.bitstring ⟨(textOf x ++ tailText xs).toArray⟩ 0 (valid_aligned _))
                  (.bitstring ⟨(pre ++ textOf x ++ tailText xs).toArray⟩ 0 (valid_aligned _))
                  (.integer pre.length) (ints done.reverse) (.cons (.atom "array") (.cons (.atom
                      "ok") .nil)) options) =
              .ok (.tuple #[ints (done ++ x :: xs), .atom "ok",
                .bitstring ⟨([] : List UInt8).toArray⟩ 0 (valid_aligned _)]) := by
          intro xs
          induction xs with
          | nil =>
            intro x pre done depth
            simp only [tailText]
            rw [element x pre [] 93 (by decide), continue_array, array_push_close]
            rw [show Term.cons (.integer x) (ints done.reverse) = ints (x :: done.reverse) from rfl, reverse1_ints]
            simp [continue_top, terminate_end]
          | cons y ys ih =>
            intro x pre done depth
            simp only [tailText]
            rw [element x pre (textOf y ++ tailText ys) 44 (by decide), continue_array,
              array_push_comma]
            have step := ih y (pre ++ textOf x ++ [44]) (done ++ [x]) depth
            have skip : (((pre ++ textOf x ++ [44]).length : Nat) : Int) = pre.length + (textOf
                x).length + 1 := by
              simp; omega
            have acc : ints (done ++ [x]).reverse = .cons (.integer x) (ints done.reverse) := by
                simp [ints]
            rw [skip, acc] at step
            simp only [List.append_assoc, List.singleton_append, List.cons_append,
              List.nil_append] at step
            simpa [Result.resolve_bind] using step

        have encode_integer : ∀ (x : Int) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth («do_encode/2» (.integer x) (.function
                0 2 #[])) =
              .ok (.bitstring ⟨(textOf x).toArray⟩ 0 (valid_aligned _)) := by
          intro x depth
          obtain ⟨first, rest, text, encoded, -, -⟩ := textOf_decimal x
          unfold «do_encode/2»
          simp only []
          rw [encoded, Result.resolve_of_isPure _ _ _ (by simp), text]

        have encode_element : ∀ (x : Int) (depth : Nat),
            Result.resolve Erlang.program.fun_table (depth + 1)
                (Term.apply (.function 0 2 #[]) #[.integer x, .function 0 2 #[]]) =
              .ok (.bitstring ⟨(textOf x).toArray⟩ 0 (valid_aligned _)) := by
          intro x depth
          obtain ⟨first, rest, text, encoded, -, -⟩ := textOf_decimal x
          rw [Erlang.program.fun_table_apply_0]
          unfold «do_encode/2»
          simp only []
          rw [encoded, Result.resolve_of_isPure _ _ _ (by simp), text]

        have list_loop_ints : ∀ (xs : List Int) (depth : Nat),
            Result.resolve Erlang.program.fun_table (depth + 1) («list_loop/2» (ints xs)
                (.function 0 2 #[])) =
              .ok (loopIodata xs) := by
          intro xs depth
          induction xs with
          | nil => simp [ints, loopIodata, «list_loop/2»]
          | cons y ys ih =>
            simp only [ints, «list_loop/2»]
            simp [Result.resolve_bind, encode_integer, ih, loopIodata]

        have flatten_loop : ∀ (xs : List Int),
            Erlang.erlang.«iolist_to_binary/1» (loopIodata xs) =
              .ok (.bitstring ⟨(tailText xs).toArray⟩ 0 (valid_aligned _)) := by
          intro xs
          induction xs with
          | nil =>
            simp only [loopIodata, tailText]
            rw [Erlang.erlang.iolist_to_binary_byte_cons 93 .nil ⟨#[]⟩ (by decide) (by decide)
              Erlang.erlang.iolist_to_binary_nil]
            rfl
          | cons y ys ih =>
            simp only [loopIodata, tailText]
            have inner := Erlang.erlang.iolist_to_binary_join _ _ _ _
              (Erlang.erlang.iolist_to_binary_binary ⟨(textOf y).toArray⟩) ih
            rw [Erlang.erlang.iolist_to_binary_byte_cons 44 _ _ (by decide) (by decide) inner]
            congr 2

        have array_start_close : ∀ (bs : List UInt8) (orig skip acc stack : Term) (len : Int),
            «array_start/7» (.bitstring ⟨((93 : UInt8) :: bs).toArray⟩ 0 (valid_aligned _)) orig
                skip acc stack options
                (.integer len) =
              (do
                let next ← Erlang.erlang.«+/2» skip (.integer len)
                let after ← Erlang.erlang.«+/2» next (.integer 1)
                «continue/7» (.bitstring ⟨bs.toArray⟩ 0 (valid_aligned _)) orig after acc stack
                    options .nil) := by
          intro bs orig skip acc stack len
          conv => lhs; unfold «array_start/7»
          simp only [matchInteger_byte, extract_some, matchEnd_byte]
          simp [matchTail, Nat.mod_one, Erlang.erlang.«=:=/2», Erlang.erlang.«or/2»]

        have decode_list : ∀ (l : List Int) (depth : Nat),
            Result.resolve Erlang.program.fun_table depth
                («decode/1» (.bitstring ⟨(listText l).toArray⟩ 0 (valid_aligned _))) = .ok (ints
                    l) := by
          intro l depth
          unfold «decode/1»
          simp only []
          cases l with
          | nil =>
            simp only [listText]
            rw [value_open, array_start_close]
            simp [continue_top, terminate_end, ints]
          | cons x xs =>
            simp only [listText]
            obtain ⟨first, rest, text, -, digits, -⟩ := textOf_decimal x
            have start : ∃ b bs, textOf x = b :: bs ∧ (b.toNat = 45 ∨ (48 ≤ b.toNat ∧ b.toNat ≤
                57)) := by
              by_cases negative : x < 0
              · exact ⟨45, first :: rest, by simp [text, negative], Or.inl rfl⟩
              · exact ⟨first, rest, by simp [text, negative], Or.inr (digits first (by simp))⟩
            obtain ⟨b, bs, head, startByte⟩ := start
            have whole := loop xs x [91] [] depth
            simp only [listText, head, List.cons_append, List.nil_append, List.singleton_append,
              List.reverse_nil, List.length_singleton] at whole ⊢
            rw [value_open, array_start_value b (bs ++ tailText xs) _ _ _ _ _ startByte]
            simp only [Result.resolve_bind, Erlang.erlang.«+/2_integers», Result.ok_bind,
              Result.resolve_of_isPure _ _ (Result.ok _) (by simp)]
            rw [show ((1 : Nat) : Int) = 1 from rfl, show ints [] = Term.nil from rfl] at whole
            rw [show (0 : Int) + 1 = 1 by rfl, whole]
            simp [ints]

        have flatten_list : ∀ (x : Int) (xs : List Int),
            Erlang.erlang.«iolist_to_binary/1»
                (.cons (.integer 91) (.cons (.bitstring ⟨(textOf x).toArray⟩ 0 (valid_aligned _))
                    (loopIodata xs))) =
              .ok (.bitstring ⟨(listText (x :: xs)).toArray⟩ 0 (valid_aligned _)) := by
          intro x xs
          have inner := Erlang.erlang.iolist_to_binary_join _ _ _ _
            (Erlang.erlang.iolist_to_binary_binary ⟨(textOf x).toArray⟩) (flatten_loop xs)
          rw [Erlang.erlang.iolist_to_binary_byte_cons 91 _ _ (by decide) (by decide) inner]
          congr 2

        have roundtrip_list : ∀ (l : List Int),
            Result.resolve Erlang.program.fun_table 100 («roundtrip/1» (ints l)) = .ok Term.true
                := by
          intro l
          simp only [«roundtrip/1», «encode/1», «encode/2», Erlang.erlang.«is_function/2»]
          simp
          unfold «do_encode/2»
          cases l with
          | nil =>
            simp [ints, «do_encode_list/2», Erlang.erlang.«is_list/1»]
            have decoded := decode_list [] 100
            simp only [listText, ints] at decoded
            simp only [Result.resolve_bind]
            rw [Erlang.erlang.iolist_to_binary_binary ⟨#[91, 93]⟩,
              Result.resolve_of_isPure _ _ _ (by simp),
              Result.ok_bind, decoded]
            simp [Erlang.erlang.«=:=/2»]
          | cons x xs =>
            simp only [ints]
            simp [Erlang.erlang.«is_list/1», «do_encode_list/2», Erlang.erlang.«is_function/2»]
            rw [encode_integer, Result.ok_bind, Result.resolve_bind,
              show (99 : Nat) = 98 + 1 from rfl, list_loop_ints xs 98, Result.ok_bind,
              Result.resolve_of_isPure _ _ _ (by simp), Result.ok_bind]
            simp only [Result.resolve_bind]
            rw [flatten_list, Result.resolve_of_isPure _ _ _ (by simp), Result.ok_bind,
              decode_list,
              Result.ok_bind]
            simp [Erlang.erlang.«=:=/2», ints]

        -- The requirement covers integers and lists of integers.
        have integers : ∀ t, «integers?/1» t = .ok Term.true → ∃ l, t = ints l := by
          intro t
          induction t using «integers?/1».induct with
          | case1 => intro; exact ⟨[], rfl⟩
          | case2 x xs ih =>
            intro h
            unfold «integers?/1» at h
            cases x <;> simp [Erlang.erlang.«is_integer/1»] at h
            rename_i n
            obtain ⟨l, rfl⟩ := ih h
            exact ⟨n :: l, rfl⟩
          | case3 t nil cons =>
            intro h
            unfold «integers?/1» at h
            split at h <;> simp_all

        apply Lynx.run_of_resolve rfl
        simp only [«json_roundtrip:requires/1»] at requires
        unfold «supported?/1» at requires
        cases data with
        | integer n => simpa [«json_roundtrip:ensures/1»] using roundtrip_integer n
        | nil => simpa [«json_roundtrip:ensures/1», ints] using roundtrip_list []
        | cons head tail =>
          simp [Erlang.erlang.«is_list/1»] at requires
          obtain ⟨l, same⟩ := integers _ requires
          rw [same]
          simpa [«json_roundtrip:ensures/1»] using roundtrip_list l
        | _ => simp [Erlang.erlang.«is_list/1»] at requires)
      """
  end
end
