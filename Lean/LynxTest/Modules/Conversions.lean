module

import Lynx.Modules.Erlang.erlang
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

end LynxTest.Modules.Conversions

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Conversions
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.erlang.Conversions
