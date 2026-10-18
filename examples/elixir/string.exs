# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/elixir/string.exs
# Verify installed String functions translated from BEAM debug information.
# Checked against Elixir 1.21.0-dev, Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/string.ex.
ExUnit.start()

defmodule StringProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def scalar?(codepoint) do
    is_integer(codepoint) and codepoint >= 0 and codepoint <= 0x10FFFF and
      (codepoint < 0xD800 or codepoint > 0xDFFF)
  end

  def prepend(codepoint, tail), do: <<codepoint::utf8, tail::binary>>

  laws "String codepoint construction and matching" do
    law next_codepoint_recovers_prefix(codepoint, tail),
      requires: scalar?(codepoint) and is_binary(tail),
      expects: String.next_codepoint(prepend(codepoint, tail)) === {<<codepoint::utf8>>, tail},
      proof: ~LEAN"""
      set_option maxRecDepth 4096 in
      cases codepoint <;> simp [«next_codepoint_recovers_prefix:requires/2», «scalar?/1»,
        Erlang.erlang.«is_integer/1»] at requires
      rename_i n
      have scalar : 0 ≤ n ∧ n ≤ 0x10ffff ∧ (n < 0xd800 ∨ 0xdfff < n) := by
        by_cases a : 0 ≤ n <;> by_cases b : n ≤ 0x10ffff <;>
          by_cases c : n < 0xd800 <;> by_cases d : 0xdfff < n <;>
          simp [Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt,
            Int.compare_eq_gt, a, b, c, d] at requires <;> omega
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le scalar.1
      have tailBinary : Erlang.erlang.«is_binary/1» tail = .ok Lynx.Term.true := by
        by_cases low : (n : Int) < 0xd800
        · simpa [scalar.1, scalar.2.1, low] using requires
        · have high : (0xdfff : Int) < n := by omega
          simpa [scalar.1, scalar.2.1, low, high, Erlang.erlang.«>/2»,
            Ordering.isGT_iff_eq_gt, Int.compare_eq_gt] using requires
      cases tail <;> simp [Erlang.erlang.«is_binary/1»] at tailBinary
      rename_i storage last valid
      rcases last with ⟨last, lastLt⟩
      cases last with
      | succ last => simp at tailBinary
      | zero =>
        change «next_codepoint_recovers_prefix:ensures/2» (.integer n)
          (.bitstring storage 0 valid) = .ok Lynx.Term.true
        open Lynx.Term.Bitstring in
          have original : ofBits (toBits storage 0) = .bitstring storage 0 valid :=
            ofBits_toBits_aligned storage
          obtain ⟨encoded, constructed, aligned, matched⟩ := matchUtf8_construct n
            (toBits storage 0) (by omega) (by omega)
          have tailAligned : (toBits storage 0).length % 8 = 0 := by
            rw [toBits_length_aligned]; omega
          have tailMatch : matchTail (ofBits (toBits storage 0)) (.atom "all") 8 = true := by
            simp only [matchTail, ofBits, pack_bitSize]
            simp [tailAligned]
          have copied : binarySegment (ofBits (toBits storage 0)) (.atom "all") 8 =
              .ok (ofBits (toBits storage 0)) := by
            simp only [binarySegment, ofBits, pack_bitSize]
            simp [tailAligned]
          rw [←original]
          simp [«next_codepoint_recovers_prefix:ensures/2», «prepend/2», constructed,
            copied, append_bits, Elixir.String.«next_codepoint/1», matched, tailMatch,
            Erlang.erlang.«=:=/2», Except.bind]
      """
  end
end
