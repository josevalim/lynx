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

private meta def rendered : Result → String
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

/-- Decimal text produced by `integer_to_binary/1` reads back as the same integer. -/
theorem integer_binary_round_trip (n : Int) :
    (Erlang.erlang.«integer_to_binary/1» (.integer n) >>= Erlang.erlang.«binary_to_integer/1») =
      .ok (.integer n) :=
  Erlang.erlang.binary_to_integer_integer_to_binary n

/-- The part spanning a whole binary is the binary itself. -/
theorem binary_part_of_whole :
    Erlang.erlang.«binary_part/3» (.bitstring ⟨#[1, 2]⟩ 0) (.integer 0) (.integer 2) =
      .ok (.bitstring ⟨#[1, 2]⟩ 0) :=
  Erlang.erlang.binary_part_whole ⟨#[1, 2]⟩

end LynxTest.Modules.Conversions

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Conversions
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Conversions
