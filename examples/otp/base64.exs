# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/base64.exs
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
ExUnit.start()

defmodule Base64ProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def encoding_contract(bytes) do
    encoded = :base64.encode(bytes)
    :base64.decode(encoded) === bytes and byte_size(encoded) === div(byte_size(bytes) + 2, 3) * 4
  end

  @lookup_tables Lynx.Lean.from_file!(Path.expand("lookup_tables.lean", __DIR__))

  laws "Base64 encoding round trip", options: [maxHeartbeats: 800_000] do
    prelude @lookup_tables
    cutoff &:base64.encode_list/4
    cutoff &:base64.decode_list/4

    law encoding_roundtrip(bytes),
      requires: is_binary(bytes),
      expects: encoding_contract(bytes),
      proof: ~LEAN"""
      open Lynx.Term.Bitstring in
        set_option maxRecDepth 8192 in
          let encodeTable : Lynx.Term := by
            run_tac do
              let some equations ← Lean.Meta.getEqnsFor? ``Erlang.base64.«encode_binary/4» |
                throwError "encoding equations were not found"
              let type := (← Lean.getConstInfo equations[0]!).type
              let some table := type.find? LookupTables.isTable |
                throwError "encoding table was not found"
              (← Lean.Elab.Tactic.getMainGoal).assign table
          let decodeTable : Lynx.Term := by
            run_tac do
              let some equations ← Lean.Meta.getEqnsFor? ``Erlang.base64.«decode_binary/4» |
                throwError "decoding equations were not found"
              let type := (← Lean.getConstInfo equations[0]!).type
              let some table := type.find? LookupTables.isTable |
                throwError "decoding table was not found"
              (← Lean.Elab.Tactic.getMainGoal).assign table
          let symbol (n : Nat) : Nat :=
            if n<26 then n+65 else if n<52 then n+71 else if n<62 then n-4 else if n=62 then 43 else 47
          let returnsInteger (computation : Except Lynx.Exception Lynx.Term) (expected : Int) : Bool :=
            match computation with
            | .ok (.integer value) => value == expected
            | _ => false
          have returnsInteger_ok (computation : Except Lynx.Exception Lynx.Term) (expected : Int)
              (returned : returnsInteger computation expected = true) :
              computation = .ok (.integer expected) := by
            cases computation <;> simp [returnsInteger] at returned
            rename_i value
            cases value <;> simp_all [returnsInteger]
          have encodeChecked : (List.range 64).all (fun n => returnsInteger
              (Erlang.erlang.«element/2» (.integer (n+1)) encodeTable) (symbol n)) = true := by
            decide
          have decodeChecked : (List.range 64).all (fun n => returnsInteger
              (Erlang.erlang.«element/2» (.integer (symbol n+1)) decodeTable) n) = true := by
            decide
          have encodeLookup (n : Nat) (bound : n<64) :
              Erlang.erlang.«element/2» (.integer (n+1)) encodeTable = .ok (.integer (symbol n)) :=
            returnsInteger_ok _ _ ((List.all_eq_true.mp encodeChecked) n (List.mem_range.mpr bound))
          have decodeLookup (n : Nat) (bound : n<64) :
              Erlang.erlang.«element/2» (.integer (symbol n+1)) decodeTable = .ok (.integer n) :=
            returnsInteger_ok _ _ ((List.all_eq_true.mp decodeChecked) n (List.mem_range.mpr bound))
          have symbolBound (n : Nat) (bound : n<64) : symbol n<256 := by
            dsimp [symbol]
            repeat' first | split | omega
          let charBits (n : Nat) := integerBits (symbol n) 8 false
          have field (n : Nat) (tail : List Bool) (bound : n<64) :
              matchInteger (ofBits (integerBits n 6 false ++ tail)) (.integer 6) 1 false false =
                some (.integer n, ofBits tail) := by
            simpa [integerBits_length, decodeInteger_integerBits,
              show 2^6=64 by decide, Nat.mod_eq_of_lt bound] using
              matchInteger_prefix (integerBits n 6 false) tail
          have okBind {α β : Type} (value : α) (next : α → Except Lynx.Exception β) :
              ((Except.ok value) >>= next) = next value := rfl
          have construct8 (n : Int) : integerSegment (.integer n) (.integer 8) 1 false =
              .ok (ofBits (integerBits n 8 false)) := integerSegment_bits n 8
          have encode48 (a b c d e f g h : Nat)
              (ha : a<64) (hb : b<64) (hc : c<64) (hd : d<64)
              (he : e<64) (hf : f<64) (hg : g<64) (hh : h<64)
              (tail acc : List Bool) :
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (integerBits a 6 false ++ (integerBits b 6 false ++
                  (integerBits c 6 false ++ (integerBits d 6 false ++
                  (integerBits e 6 false ++ (integerBits f 6 false ++
                  (integerBits g 6 false ++ (integerBits h 6 false ++ tail))))))))) (ofBits acc) =
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true (ofBits tail)
                (ofBits (acc ++ (charBits a ++ (charBits b ++ (charBits c ++ (charBits d ++
                  (charBits e ++ (charBits f ++ (charBits g ++ charBits h))))))))) := by
            conv => lhs; unfold Erlang.base64.«encode_binary/4»
            lynx_fold_table encodeTable
            simp (disch := omega) only [extract_some,
              field, matchTail_bits, Erlang.erlang.«+/2_integers»,
              Int.natCast_add, Int.cast_ofNat_Int, encodeLookup,
              okBind, Except.bind, construct8, binarySegment_bits, append_bits]
            try rfl
          have take6 (bits : List Bool) (enough : 6≤bits.length) :
              matchInteger (ofBits bits) (.integer 6) 1 false false =
                some (.integer (decodeInteger (bits.take 6) false), ofBits (bits.drop 6)) :=
            matchInteger_take bits 6 enough
          have short6 (bits : List Bool) (short : bits.length<6) :
              matchInteger (ofBits bits) (.integer 6) 1 false false = none := by
            simp [matchInteger, ofBits, pack_toBits, show ¬6≤bits.length by omega]
          have notEnd (bits : List Bool) (positive : 0<bits.length) :
              matchEnd (ofBits bits) = false := by
            simp [matchEnd_bits, show bits.length≠0 by omega]
          have encode24 (a b c d : Nat) (ha : a<64) (hb : b<64) (hc : c<64) (hd : d<64)
              (tail acc : List Bool) (short : tail.length<24) (aligned : tail.length%8=0) :
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (integerBits a 6 false ++ (integerBits b 6 false ++
                  (integerBits c 6 false ++ (integerBits d 6 false ++ tail))))) (ofBits acc) =
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true (ofBits tail)
                (ofBits (acc ++ (charBits a ++ (charBits b ++ (charBits c ++ charBits d))))) := by
            have noEmpty := notEnd
              (integerBits a 6 false ++ (integerBits b 6 false ++
                (integerBits c 6 false ++ (integerBits d 6 false ++ tail))))
              (by simp only [List.length_append, integerBits_length]; omega)
            have tailMatch (i : Nat) :
                matchInteger (ofBits (tail.drop i)) (.integer 6) 1 false false =
                  if 6≤(tail.drop i).length then
                    some (.integer (decodeInteger ((tail.drop i).take 6) false), ofBits ((tail.drop i).drop 6))
                  else none := by
              by_cases enough : 6≤(tail.drop i).length
              · simp only [enough, ↓reduceIte]; exact take6 _ enough
              · simp only [enough, ↓reduceIte]; exact short6 _ (by omega)
            have tailMatch0 := tailMatch 0
            simp only [List.drop_zero] at tailMatch0
            have lengths : tail.length=0 ∨ tail.length=8 ∨ tail.length=16 := by omega
            rcases lengths with empty | eight | sixteen
            all_goals
              conv => lhs; unfold Erlang.base64.«encode_binary/4»
              lynx_fold_table encodeTable
              simp (disch := omega) only [extract_some, extract_none, noEmpty,
                if_pos, if_neg, field, tailMatch0, tailMatch,
                List.length_drop, List.drop_drop, matchTail_bits,
                Erlang.erlang.«+/2_integers», encodeLookup, okBind, Except.bind,
                construct8, binarySegment_bits, append_bits]
              rfl
          have field8 (n : Nat) (tail : List Bool) (bound : n<256) :
              matchInteger (ofBits (integerBits n 8 false ++ tail)) (.integer 8) 1 false false =
                some (.integer n, ofBits tail) := by
            simpa [integerBits_length, decodeInteger_integerBits,
              show 2^8=256 by decide, Nat.mod_eq_of_lt bound] using
              matchInteger_prefix (integerBits n 8 false) tail
          have construct6 (n : Int) : integerSegment (.integer n) (.integer 6) 1 false =
              .ok (ofBits (integerBits n 6 false)) := integerSegment_bits n 6
          have decode32 (a b c d : Nat) (ha : a<64) (hb : b<64) (hc : c<64) (hd : d<64)
              (tail acc : List Bool) :
              Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (charBits a ++ (charBits b ++ (charBits c ++ (charBits d ++ tail))))) (ofBits acc) =
              Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true (ofBits tail)
                (ofBits (acc ++ (integerBits a 6 false ++ (integerBits b 6 false ++
                  (integerBits c 6 false ++ integerBits d 6 false))))) := by
            have ha' := symbolBound a ha
            have hb' := symbolBound b hb
            have hc' := symbolBound c hc
            have hd' := symbolBound d hd
            conv => lhs; unfold Erlang.base64.«decode_binary/4»
            lynx_fold_table decodeTable
            simp (disch := omega) only [extract_some, charBits, field8, symbolBound, matchTail_bits,
              Erlang.erlang.«+/2_integers», decodeLookup, okBind, Except.bind,
              construct6, binarySegment_bits, append_bits]
            try rfl
          have field2 (n : Nat) (bound : n<4) :
              matchInteger (ofBits (integerBits n 2 false)) (.integer 2) 1 false false =
                some (.integer n, ofBits []) := by
            simpa [integerBits_length, decodeInteger_integerBits, Nat.mod_eq_of_lt bound] using
              matchInteger_prefix (integerBits n 2 false) []
          have left4 (n : Nat) : Erlang.erlang.«bsl/2» (.integer n) (.integer 4) =
              .ok (.integer ((n*16 : Nat) : Int)) := by
            simp [Erlang.erlang.«bsl/2», Int.shiftLeft_eq, Int.natCast_mul]
          let pad := integerBits 61 8 false
          have encode8 (a b : Nat) (ha : a<64) (hb : b<4) (acc : List Bool) :
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (integerBits a 6 false ++ integerBits b 2 false)) (ofBits acc) =
              .ok (ofBits (acc ++ (charBits a ++ (charBits (b*16) ++ (pad ++ pad))))) := by
            have noEmpty := notEnd (integerBits a 6 false ++ integerBits b 2 false)
              (by simp only [List.length_append, integerBits_length]; omega)
            conv => lhs; unfold Erlang.base64.«encode_binary/4»
            lynx_fold_table encodeTable
            simp (disch := (try simp only [integerBits_length]); omega) only
              [extract_some, extract_none, noEmpty, short6, field, matchTail_bits, field2, matchEnd_bits,
               List.length_nil, beq_self_eq_true, Lynx.Term.true, left4, Erlang.erlang.«+/2_integers», encodeLookup,
               okBind, Except.bind, construct8, binarySegment_bits, append_bits]
            rfl
          have field4 (n : Nat) (bound : n<16) :
              matchInteger (ofBits (integerBits n 4 false)) (.integer 4) 1 false false =
                some (.integer n, ofBits []) := by
            simpa [integerBits_length, decodeInteger_integerBits, Nat.mod_eq_of_lt bound] using
              matchInteger_prefix (integerBits n 4 false) []
          have left2 (n : Nat) : Erlang.erlang.«bsl/2» (.integer n) (.integer 2) =
              .ok (.integer ((n*4 : Nat) : Int)) := by
            simp [Erlang.erlang.«bsl/2», Int.shiftLeft_eq, Int.natCast_mul]
          have take2 (bits : List Bool) (enough : 2≤bits.length) :
              matchInteger (ofBits bits) (.integer 2) 1 false false =
                some (.integer (decodeInteger (bits.take 2) false), ofBits (bits.drop 2)) :=
            matchInteger_take bits 2 enough
          have encode16 (a b c : Nat) (ha : a<64) (hb : b<64) (hc : c<16) (acc : List Bool) :
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (integerBits a 6 false ++ (integerBits b 6 false ++ integerBits c 4 false)))
                (ofBits acc) =
              .ok (ofBits (acc ++ (charBits a ++ (charBits b ++ (charBits (c*4) ++ pad))))) := by
            have noEmpty := notEnd
              (integerBits a 6 false ++ (integerBits b 6 false ++ integerBits c 4 false))
              (by simp only [List.length_append, integerBits_length]; omega)
            conv => lhs; unfold Erlang.base64.«encode_binary/4»
            lynx_fold_table encodeTable
            simp (disch := (try simp only [List.length_append, List.length_drop, integerBits_length]); omega) only
              [extract_some, extract_none, noEmpty,
               short6, field, matchTail_bits, take2, field4, notEnd, matchEnd_bits,
               List.length_nil, beq_self_eq_true, Lynx.Term.true, left2, Erlang.erlang.«+/2_integers», encodeLookup,
               okBind, Except.bind, construct8, binarySegment_bits, append_bits]
            rfl
          have encodeEmpty (acc : List Bool) :
              Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true (ofBits []) (ofBits acc) =
                .ok (ofBits acc) := by
            conv => lhs; unfold Erlang.base64.«encode_binary/4»
            lynx_fold_table encodeTable
            rfl
          have decodeEmpty (acc : List Bool) :
              Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true (ofBits []) (ofBits acc) =
                .ok (ofBits acc) := by
            conv => lhs; unfold Erlang.base64.«decode_binary/4»
            lynx_fold_table decodeTable
            rfl
          have exact8 (n : Nat) (bound : n<256) :
              matchInteger (ofBits (integerBits n 8 false)) (.integer 8) 1 false false =
                some (.integer n, ofBits []) := by
            simpa using field8 n [] bound
          have paddingLookup : Erlang.erlang.«element/2» (.integer 62) decodeTable =
              .ok (.atom "eq") := by rfl
          have wsEmpty (acc : List Bool) :
              Erlang.base64.«only_ws_binary/4» (.integer 1) Lynx.Term.true (ofBits []) (ofBits acc) =
                .ok (ofBits acc) := by
            conv => lhs; unfold Erlang.base64.«only_ws_binary/4»
            rfl
          have construct2 (n : Int) : integerSegment (.integer n) (.integer 2) 1 false =
              .ok (ofBits (integerBits n 2 false)) := integerSegment_bits n 2
          have right4 (n : Nat) : Erlang.erlang.«bsr/2» (.integer ((n*16:Nat):Int)) (.integer 4) =
              .ok (.integer n) := by
            simp only [Erlang.erlang.«bsr/2», ←Int.natCast_shiftRight]
            simp [Nat.shiftRight_eq_div_pow]
          have right4Int (n : Nat) : Erlang.erlang.«bsr/2» (.integer ((n:Int)*16)) (.integer 4) =
              .ok (.integer n) := by simpa only [Int.natCast_mul, Int.cast_ofNat_Int] using right4 n
          dsimp only [extract_some, extract_none, Lynx.Term.true] at wsEmpty
          have padPrefix (tail : List Bool) :
              matchInteger (ofBits (pad++tail)) (.integer 8) 1 false false =
                some (.integer 61, ofBits tail) := field8 61 tail (by decide)
          have padExact : matchInteger (ofBits pad) (.integer 8) 1 false false =
              some (.integer 61, ofBits []) := exact8 61 (by decide)
          have decode8 (a b : Nat) (ha : a<64) (hb : b<4) (acc : List Bool) :
              Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (charBits a ++ (charBits (b*16) ++ (pad ++ pad)))) (ofBits acc) =
              .ok (ofBits (acc ++ (integerBits a 6 false ++ integerBits b 2 false))) := by
            have ha' := symbolBound a ha
            have hb' := symbolBound (b*16) (by omega)
            conv => lhs; unfold Erlang.base64.«decode_binary/4»
            lynx_fold_table decodeTable
            simp (disch := omega) only [extract_some,
              charBits, field8, exact8, padPrefix, padExact, matchTail_bits,
              Erlang.erlang.«+/2_integers», Int.reduceAdd, decodeLookup, paddingLookup, okBind, Except.bind]
            conv => lhs; unfold Erlang.base64.«dec_bin/8»
            simp [Erlang.erlang.«=:=/2», Lynx.Term.true, Lynx.Except.guard,
              right4Int, okBind, Except.bind,
              construct2, construct6, binarySegment_bits, append_bits, wsEmpty]
          have construct4 (n : Int) : integerSegment (.integer n) (.integer 4) 1 false =
              .ok (ofBits (integerBits n 4 false)) := integerSegment_bits n 4
          have right2 (n : Nat) : Erlang.erlang.«bsr/2» (.integer ((n*4:Nat):Int)) (.integer 2) =
              .ok (.integer n) := by
            simp only [Erlang.erlang.«bsr/2», ←Int.natCast_shiftRight]
            simp [Nat.shiftRight_eq_div_pow]
          have right2Int (n : Nat) : Erlang.erlang.«bsr/2» (.integer ((n:Int)*4)) (.integer 2) =
              .ok (.integer n) := by simpa only [Int.natCast_mul, Int.cast_ofNat_Int] using right2 n
          have decode16 (a b c : Nat) (ha : a<64) (hb : b<64) (hc : c<16) (acc : List Bool) :
              Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true
                (ofBits (charBits a ++ (charBits b ++ (charBits (c*4) ++ pad)))) (ofBits acc) =
              .ok (ofBits (acc ++ (integerBits a 6 false ++ (integerBits b 6 false ++ integerBits c 4 false)))) := by
            have ha' := symbolBound a ha
            have hb' := symbolBound b hb
            have hc' := symbolBound (c*4) (by omega)
            conv => lhs; unfold Erlang.base64.«decode_binary/4»
            lynx_fold_table decodeTable
            simp (disch := omega) only [extract_some,
              charBits, field8, exact8, padExact, matchTail_bits,
              Erlang.erlang.«+/2_integers», Int.reduceAdd, decodeLookup, paddingLookup, okBind, Except.bind]
            conv => lhs; unfold Erlang.base64.«dec_bin/8»
            simp [Erlang.erlang.«=:=/2», Lynx.Term.true, Lynx.Except.guard,
              right2Int, okBind, Except.bind,
              construct4, construct6, binarySegment_bits, append_bits, wsEmpty]
          have divide (bits : List Bool) (width : Nat) (enough : width≤bits.length) :
              ∃ n : Nat, ∃ rest : List Bool, n<2^width ∧
                bits=integerBits n width false++rest ∧ rest.length=bits.length-width := by
            have reconstructed : integerBits (decodeInteger (bits.take width) false) width false = bits.take width := by
              simpa only [List.length_take_of_le enough] using integerBits_decodeInteger (bits.take width)
            refine ⟨decodeInteger (bits.take width) false, bits.drop width, ?_, ?_, by simp⟩
            · simpa only [List.length_take_of_le enough] using decodeInteger_lt (bits.take width)
            · rw [reconstructed, List.take_append_drop]
          have byLength : ∀ size, ∀ bits : List Bool, bits.length=size → size%8=0 →
              ∃ encoded : List Bool,
                encoded.length=32*((bits.length+16)/24) ∧
                (∀ acc, Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true
                  (ofBits bits) (ofBits acc) = .ok (ofBits (acc++encoded))) ∧
                (∀ acc, Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true
                  (ofBits encoded) (ofBits acc) = .ok (ofBits (acc++bits))) := by
            intro size
            induction size using Nat.strongRecOn with
            | ind size ih =>
              intro bits length aligned
              by_cases large : 48≤size
              · obtain ⟨a, resta, ha, eqa, lena⟩ := divide bits 6 (by omega)
                obtain ⟨b, restb, hb, eqb, lenb⟩ := divide resta 6 (by omega)
                obtain ⟨c, restc, hc, eqc, lenc⟩ := divide restb 6 (by omega)
                obtain ⟨d, restd, hd, eqd, lend⟩ := divide restc 6 (by omega)
                obtain ⟨e, reste, he, eqe, lene⟩ := divide restd 6 (by omega)
                obtain ⟨f, restf, hf, eqf, lenf⟩ := divide reste 6 (by omega)
                obtain ⟨g, restg, hg, eqg, leng⟩ := divide restf 6 (by omega)
                obtain ⟨h, resth, hh, eqh, lenh⟩ := divide restg 6 (by omega)
                obtain ⟨encoded, encodedLength, enc, dec⟩ := ih resth.length (by omega) resth rfl (by omega)
                refine ⟨charBits a ++ (charBits b ++ (charBits c ++ (charBits d ++ (charBits e ++ (charBits f ++ (charBits g ++ (charBits h ++ (encoded)))))))), ?_, ?_, ?_⟩
                · simp only [List.length_append, charBits, integerBits_length]
                  omega
                · intro acc
                  rw [eqa, eqb, eqc, eqd, eqe, eqf, eqg, eqh]
                  rw [encode48 a b c d e f g h ha hb hc hd he hf hg hh resth acc, enc]
                  simp only [List.append_assoc]
                · intro acc
                  rw [decode32 a b c d ha hb hc hd]
                  rw [decode32 e f g h he hf hg hh]
                  rw [dec]
                  simp only [eqa, eqb, eqc, eqd, eqe, eqf, eqg, eqh, List.append_assoc]
              · by_cases medium : 24≤size
                · obtain ⟨a, resta, ha, eqa, lena⟩ := divide bits 6 (by omega)
                  obtain ⟨b, restb, hb, eqb, lenb⟩ := divide resta 6 (by omega)
                  obtain ⟨c, restc, hc, eqc, lenc⟩ := divide restb 6 (by omega)
                  obtain ⟨d, restd, hd, eqd, lend⟩ := divide restc 6 (by omega)
                  obtain ⟨encoded, encodedLength, enc, dec⟩ := ih restd.length (by omega) restd rfl (by omega)
                  refine ⟨charBits a ++ (charBits b ++ (charBits c ++ (charBits d ++ (encoded)))), ?_, ?_, ?_⟩
                  · simp only [List.length_append, charBits, integerBits_length]
                    omega
                  · intro acc
                    rw [eqa, eqb, eqc, eqd]
                    rw [encode24 a b c d ha hb hc hd restd acc (by omega) (by omega), enc]
                    simp only [List.append_assoc]
                  · intro acc
                    rw [decode32 a b c d ha hb hc hd]
                    rw [dec]
                    simp only [eqa, eqb, eqc, eqd, List.append_assoc]
                · have small : size=0 ∨ size=8 ∨ size=16 := by omega
                  rcases small with zero | eight | sixteen
                  · have empty : bits=[] := List.eq_nil_of_length_eq_zero (by omega)
                    subst bits
                    refine ⟨[], rfl, ?_, ?_⟩
                    · intro acc; simpa using encodeEmpty acc
                    · intro acc; simpa using decodeEmpty acc
                  · obtain ⟨a, resta, ha, eqa, lena⟩ := divide bits 6 (by omega)
                    obtain ⟨b, restb, hb, eqb, lenb⟩ := divide resta 2 (by omega)
                    have empty : restb=[] := List.eq_nil_of_length_eq_zero (by omega)
                    subst restb
                    have represented : bits = integerBits a 6 false ++ (integerBits b 2 false) := by
                      simp only [eqa, eqb, List.append_nil]
                    refine ⟨charBits a ++ (charBits (b*16) ++ (pad ++ (pad))), ?_, ?_, ?_⟩
                    · simp only [List.length_append, charBits, pad, integerBits_length]
                      omega
                    · intro acc
                      rw [represented, encode8 a b ha hb]
                    · intro acc
                      rw [decode8 a b ha hb, represented]
                  · obtain ⟨a, resta, ha, eqa, lena⟩ := divide bits 6 (by omega)
                    obtain ⟨b, restb, hb, eqb, lenb⟩ := divide resta 6 (by omega)
                    obtain ⟨c, restc, hc, eqc, lenc⟩ := divide restb 4 (by omega)
                    have empty : restc=[] := List.eq_nil_of_length_eq_zero (by omega)
                    subst restc
                    have represented : bits = integerBits a 6 false ++ (integerBits b 6 false ++ (integerBits c 4 false)) := by
                      simp only [eqa, eqb, eqc, List.append_nil]
                    refine ⟨charBits a ++ (charBits b ++ (charBits (c*4) ++ (pad))), ?_, ?_, ?_⟩
                    · simp only [List.length_append, charBits, pad, integerBits_length]
                      omega
                    · intro acc
                      rw [represented, encode16 a b c ha hb hc]
                    · intro acc
                      rw [decode16 a b c ha hb hc, represented]
          cases bytes <;> simp [«encoding_roundtrip:requires/1», Erlang.erlang.«is_binary/1»] at requires
          rename_i storage last valid
          rcases last with ⟨last, lastLt⟩
          cases last with
          | succ last => simp [Erlang.erlang.«is_binary/1»] at requires
          | zero =>
            change «encoding_roundtrip:ensures/1» (.bitstring storage 0 valid) = .ok Lynx.Term.true
            let bits := toBits storage 0
            have bitLength : bits.length=storage.size*8 := toBits_length_aligned storage
            have represented : ofBits bits=.bitstring storage 0 valid := ofBits_toBits_aligned storage
            obtain ⟨encoded, encodedLength, enc, dec⟩ := byLength bits.length bits rfl (by omega)
            have encodedAligned : encoded.length%8=0 := by omega
            have encodedLast : (⟨encoded.length%8, Nat.mod_lt _ (by decide)⟩ : Fin 8)=0 := Fin.ext encodedAligned
            have encodedBinary : ofBits encoded=.bitstring (pack encoded) 0 (valid_aligned _) := by
              simp only [ofBits]
              congr 1
            have encodedReturned : Erlang.base64.«encode/1» (.bitstring storage 0 valid) = .ok (ofBits encoded) := by
              simp only [Erlang.base64.«encode/1», Erlang.base64.«encode/2»]
              change Erlang.base64.«encode_binary/4» (.integer 1) Lynx.Term.true
                (.bitstring storage 0 valid) (ofBits []) = _
              simpa only [represented, List.nil_append] using enc []
            have decodedReturned : Erlang.base64.«decode/1» (ofBits encoded) = .ok (.bitstring storage 0 valid) := by
              rw [encodedBinary]
              simp only [Erlang.base64.«decode/1», Erlang.base64.«decode/2»]
              change Erlang.base64.«decode_binary/4» (.integer 1) Lynx.Term.true
                (.bitstring (pack encoded) 0 (valid_aligned _)) (ofBits []) = _
              simpa only [encodedBinary, represented, List.nil_append]
                using dec []
            have encodedSize : (pack encoded).size=((storage.size+2)/3)*4 := by
              rw [pack_size]
              omega
            have integerSize : ((pack encoded).size : Int) = ((storage.size:Int)+2).tdiv 3*4 := by
              have result := congrArg (fun value : Nat => (value:Int)) encodedSize
              simpa only [Int.natCast_mul, Int.natCast_ediv, Int.natCast_add, Int.cast_ofNat_Int,
                Int.tdiv_eq_ediv_of_nonneg (show 0≤(storage.size:Int)+2 by omega)] using result
            simp only [«encoding_roundtrip:ensures/1», «encoding_contract/1»]
            rw [encodedReturned]
            simp only [Lynx.Except.ok_bind, decodedReturned]
            simp [Erlang.erlang.«=:=/2», Lynx.Term.true, Erlang.erlang.«byte_size/1»,
              ofBits, Erlang.erlang.«+/2_integers», Erlang.erlang.«div/2», Erlang.erlang.«*/2_integers»,
              integerSize]
            simpa only [pack_size, Int.natCast_ediv, Int.natCast_add, Int.cast_ofNat_Int] using integerSize
      """
  end
end
