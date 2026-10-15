module

import Lynx.Term.Bitstring
public meta import LynxTest.ProofAudit

namespace LynxTest.Term.Bitstring

open Lynx.Term.Bitstring

theorem packing_preserves_bits (input : List Bool) :
    toBits (pack input) ⟨input.length % 8, Nat.mod_lt _ (by decide)⟩ = input :=
  pack_toBits input

theorem packing_preserves_size (input : List Bool) :
    bitSize (pack input) ⟨input.length % 8, Nat.mod_lt _ (by decide)⟩ = input.length :=
  pack_bitSize input

theorem packing_pads_low_bits :
    pack [] = ⟨#[]⟩ ∧
    pack [true] = ⟨#[0x80]⟩ ∧
    pack [true, false, true] = ⟨#[0xa0]⟩ ∧
    pack (List.replicate 8 true) = ⟨#[0xff]⟩ ∧
    pack (List.replicate 9 true) = ⟨#[0xff, 0x80]⟩ := by
  repeat first | apply And.intro | rfl

end LynxTest.Term.Bitstring

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Bitstring
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Bitstring
