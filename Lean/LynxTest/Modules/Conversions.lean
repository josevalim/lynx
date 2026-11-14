module

import Lynx.Modules.Erlang.erlang
meta import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit

namespace LynxTest.Modules.Conversions
open Lynx

-- The iodata grammar permits arbitrarily nested lists, binary tails, and byte
-- elements. Integer tails and partial bytes are outside that grammar.
inductive Flattens : Term → ByteArray → Prop
  | binary (bytes : ByteArray) : Flattens (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes)) bytes
  | nil : Flattens .nil ⟨#[]⟩
  | byte (value : Int) (tail : Term) (bytes : ByteArray)
      (lower : 0 ≤ value) (upper : value ≤ 255) (rest : Flattens tail bytes) :
      Flattens (.cons (.integer value) tail) (ByteArray.mk #[UInt8.ofNat value.toNat] ++ bytes)
  | nested (head tail : Term) (a b : ByteArray) (first : Flattens head a) (rest : Flattens tail b) :
      Flattens (.cons head tail) (a ++ b)

theorem iodata_total_and_exact (input : Term) (bytes : ByteArray) (valid : Flattens input bytes) :
    Erlang.erlang.«iolist_to_binary/1» input =
      .ok (.bitstring bytes 0 (Term.Bitstring.valid_aligned bytes)) := by
  induction valid with
  | binary bytes => exact Erlang.erlang.iolist_to_binary_binary bytes
  | nil => exact Erlang.erlang.iolist_to_binary_nil
  | byte value tail bytes lower upper _ ih =>
    exact Erlang.erlang.iolist_to_binary_byte_cons value tail bytes lower upper ih
  | nested head tail a b _ _ first rest =>
    exact Erlang.erlang.iolist_to_binary_join head tail a b first rest

/-! Number conversions, checked against Erlang/OTP 29.1.2. -/

private meta def binary (text : String) : Term := .bitstring text.toUTF8 0 (Term.Bitstring.valid_aligned _)

private meta def rendered : Except Exception Term → String
  | .ok (.integer value) => toString value
  | .ok (.float value) =>
    match Erlang.erlang.«float_to_binary/2» (.float value) (.cons (.atom "short") .nil) with
    | .ok (.bitstring bytes 0 _) => String.fromUTF8! bytes
    | _ => "invalid"
  | .ok (.bitstring bytes 0 _) =>
    match String.fromUTF8? bytes with
    | some text => text
    | none => String.ofList (bytes.toList.map fun byte => Char.ofNat byte.toNat)
  | .error (.error (.atom "badarg")) => "badarg"
  | _ => "invalid"

private meta def integerCases : List (String × String) := [  ("+12", "12"),
  ("-0", "0"),
  ("007", "7"),
  ("", "badarg"),
  ("-", "badarg"),
  ("1_000", "badarg"),
  (" 1", "badarg"),
  ("1 ", "badarg"),
  ("1.0", "badarg"),
  ("123456789012345678901234567890", "123456789012345678901234567890"),
  ("--1", "badarg"),
  ("+-1", "badarg"),
  ("0x10", "badarg")]
#guard integerCases.all fun (input, expected) =>
  rendered (Erlang.erlang.«binary_to_integer/1» (binary input)) == expected

-- Float syntax, overflow to `badarg`, underflow, and rounding at the subnormal midpoint.
private meta def floatCases : List (String × String) := [
  ("1.0", "1.0"),
  ("1e5", "badarg"),
  ("1.e5", "badarg"),
  (".5", "badarg"),
  ("1.0E+5", "1.0e5"),
  ("1.0e400", "badarg"),
  ("-0.0", "-0.0"),
  ("+1.5", "1.5"),
  ("1.0e-400", "0.0"),
  ("1.5e", "badarg"),
  ("1.5e+", "badarg"),
  ("1", "badarg"),
  ("0.1e1_0", "badarg"),
  ("1.7976931348623157e308", "1.7976931348623157e308"),
  ("1.7976931348623159e308", "badarg"),
  ("2.4703282292062327e-324", "0.0"),
  ("2.4703282292062328e-324", "5.0e-324"),
  ("00.10", "0.1")]
#guard floatCases.all fun (input, expected) =>
  rendered (Erlang.erlang.«binary_to_float/1» (binary input)) == expected

-- Shortest digits, notation choice and its tie, and scientific notation from 2 ^ 53.
private meta def shortCases : List (String × String) := [
  ("0.0", "0.0"),
  ("-0.0", "-0.0"),
  ("4.9406564584124654e-324", "5.0e-324"),
  ("1.7976931348623157e308", "1.7976931348623157e308"),
  ("100.0", "100.0"),
  ("1000.0", "1.0e3"),
  ("1230.0", "1230.0"),
  ("12300.0", "1.23e4"),
  ("0.0012", "0.0012"),
  ("0.00012", "1.2e-4"),
  ("0.1", "0.1"),
  ("0.3", "0.3"),
  ("123456.0", "123456.0"),
  ("12345.678", "12345.678"),
  ("1.0e23", "1.0e23"),
  ("9.999999999999999e22", "1.0e23"),
  ("9007199254740991.0", "9007199254740991.0"),
  ("9007199254740992.0", "9.007199254740992e15"),
  ("-1230.0", "-1230.0"),
  ("2.5e-7", "2.5e-7")]
#guard shortCases.all fun (input, expected) =>
  rendered (Erlang.erlang.«binary_to_float/1» (binary input)) == expected

#guard rendered (Erlang.erlang.«atom_to_binary/2» (.atom "héllo") (.atom "utf8")) == "héllo"
#guard rendered (Erlang.erlang.«atom_to_binary/2» (.atom "café") (.atom "latin1")) == "caf\xe9"
#guard rendered (Erlang.erlang.«atom_to_binary/2» (.atom "π") (.atom "latin1")) == "badarg"

/-! Atoms from binaries, checked against Erlang/OTP 29.1.2: UTF-8 without overlong forms,
surrogates, or code points above U+10FFFF, and at most 255 characters. -/

private meta def bytes (values : List Nat) : Term :=
  .bitstring ⟨(values.map UInt8.ofNat).toArray⟩ 0 (Term.Bitstring.valid_aligned _)

private meta def atomCodes : Except Exception Term → String
  | .ok (.atom name) => toString (name.toList.map Char.toNat)
  | .error (.error (.atom error)) => error
  | _ => "invalid"

private meta def atomCases : List (List Nat × String × String) := [
  ([], "[]", "[]"),
  ([104, 105], "[104, 105]", "[104, 105]"),
  ([0xC0, 0x80], "badarg", "[192, 128]"),
  ([0xC2, 0x80], "[128]", "[194, 128]"),
  ([0xE0, 0x9F, 0x80], "badarg", "[224, 159, 128]"),
  ([0xE0, 0xA0, 0x80], "[2048]", "[224, 160, 128]"),
  ([0xED, 0xA0, 0x80], "badarg", "[237, 160, 128]"),
  ([0xED, 0x9F, 0xBF], "[55295]", "[237, 159, 191]"),
  ([0xF0, 0x8F, 0x80, 0x80], "badarg", "[240, 143, 128, 128]"),
  ([0xF0, 0x90, 0x80, 0x80], "[65536]", "[240, 144, 128, 128]"),
  ([0xF4, 0x8F, 0xBF, 0xBF], "[1114111]", "[244, 143, 191, 191]"),
  ([0xF4, 0x90, 0x80, 0x80], "badarg", "[244, 144, 128, 128]"),
  ([0xF5, 0x80, 0x80, 0x80], "badarg", "[245, 128, 128, 128]"),
  ([0x80], "badarg", "[128]"),
  ([0xC3], "badarg", "[195]"),
  (List.replicate 256 97, "system_limit", "system_limit"),
  (List.replicate 255 97 ++ [0xFF], "system_limit", "system_limit"),
  (List.replicate 254 97 ++ [0xFF], "badarg", toString (List.replicate 254 97 ++ [255])),
  (List.replicate 1021 97, "system_limit", "system_limit"),
  ((List.replicate 300 [0xC3, 0xA9]).flatten, "system_limit", "system_limit")]

#guard atomCases.all fun (input, utf8, latin1) =>
  atomCodes (Erlang.erlang.«binary_to_atom/2» (bytes input) (.atom "utf8")) == utf8 &&
    atomCodes (Erlang.erlang.«binary_to_atom/2» (bytes input) (.atom "unicode")) == utf8 &&
    atomCodes (Erlang.erlang.«binary_to_atom/2» (bytes input) (.atom "latin1")) == latin1

#guard atomCodes (Erlang.erlang.«binary_to_atom/2» (bytes (List.replicate 255 97)) (.atom "utf8")) ==
  toString (List.replicate 255 97)
#guard atomCodes (Erlang.erlang.«binary_to_atom/1» (bytes [104, 105])) == "[104, 105]"
#guard atomCodes (Erlang.erlang.«binary_to_atom/2» (bytes [104]) (.atom "ascii")) == "badarg"
#guard atomCodes (Erlang.erlang.«binary_to_atom/2» (.atom "a") (.atom "utf8")) == "badarg"
#guard atomCodes (Erlang.erlang.«binary_to_atom/2»
  (.bitstring ⟨#[128]⟩ 1 (by decide)) (.atom "utf8")) == "badarg"

theorem tuple_to_list_elements :
    Erlang.erlang.«tuple_to_list/1» (.tuple #[.atom "a", .integer 1]) =
      .ok (.cons (.atom "a") (.cons (.integer 1) .nil)) ∧
    Erlang.erlang.«tuple_to_list/1» (.tuple #[]) = .ok .nil ∧
    Erlang.erlang.«tuple_to_list/1» .nil = .error (.error (.atom "badarg")) := by
  refine ⟨rfl, rfl, rfl⟩

/-- Decimal text produced by `integer_to_binary/1` reads back as the same integer. -/
theorem integer_binary_round_trip (n : Int) :
    (Erlang.erlang.«integer_to_binary/1» (.integer n) >>= Erlang.erlang.«binary_to_integer/1») =
      .ok (.integer n) :=
  Erlang.erlang.binary_to_integer_integer_to_binary n

/-- Shortest float text produced by `float_to_binary/2` reads back as the same float. -/
theorem float_binary_round_trip (value : Lynx.Term.FiniteFloat) :
    (Erlang.erlang.«float_to_binary/2» (.float value) (.cons (.atom "short") .nil) >>=
        Erlang.erlang.«binary_to_float/1») = .ok (.float value) :=
  Erlang.erlang.binary_to_float_float_to_binary value

/-- The part spanning a whole binary is the binary itself. -/
theorem binary_part_of_whole :
    Erlang.erlang.«binary_part/3» (.bitstring ⟨#[1, 2]⟩ 0) (.integer 0) (.integer 2) =
      .ok (.bitstring ⟨#[1, 2]⟩ 0) :=
  Erlang.erlang.binary_part_whole ⟨#[1, 2]⟩

end LynxTest.Modules.Conversions

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Conversions
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Conversions
