# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/binary.exs
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1).
# encode_hex/2 and decode_hex/1 are Erlang implementations in this OTP release.
ExUnit.start()

defmodule BinaryProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def hex_contract(bytes, mode) do
    encoded = :binary.encode_hex(bytes, mode)
    :binary.decode_hex(encoded) === bytes and byte_size(encoded) === 2 * byte_size(bytes)
  end

  @lookup_tables Lynx.Lean.from_file!(Path.expand("lookup_tables.lean", __DIR__))

  laws "hexadecimal encoding round trip", options: [maxHeartbeats: 1_000_000] do
    prelude @lookup_tables

    law hex_roundtrip(bytes, mode),
      requires: is_binary(bytes) and (mode === :uppercase or mode === :lowercase),
      expects: hex_contract(bytes, mode),
      proof: ~LEAN"""
      open Lynx.Term.Bitstring in
        set_option maxRecDepth 16384 in
          let encodeTable : Lynx.Term := by
            run_tac do
              let some equations ← Lean.Meta.getEqnsFor? ``Erlang.binary.«encode_hex2/3» |
                throwError "encoding equations were not found"
              let body := (← Lean.getConstInfo equations[0]!).type
              let some table := body.find? LookupTables.isTable |
                throwError "encoding table was not found"
              (← Lean.Elab.Tactic.getMainGoal).assign table
          let decodeTable : Lynx.Term := by
            run_tac do
              let some equations ← Lean.Meta.getEqnsFor? ``Erlang.binary.«decode_hex2/2» |
                throwError "decoding equations were not found"
              let body := (← Lean.getConstInfo equations[0]!).type
              let some table := body.find? LookupTables.isTable |
                throwError "decoding table was not found"
              (← Lean.Elab.Tactic.getMainGoal).assign table
          let offset (lower : Bool) : Int := if lower then 257 else 1
          let digit (lower : Bool) (n : Nat) : Nat :=
            if n<10 then n+48 else n+(if lower then 87 else 55)
          let hexValue (lower : Bool) (n : Nat) : Nat :=
            digit lower (n/16)*256+digit lower (n%16)
          let returnsInteger (computation : Lynx.Result) (expected : Int) : Bool :=
            match computation with
            | .ok (.integer value) => value == expected
            | _ => false
          have returnsInteger_ok (computation : Lynx.Result) (expected : Int)
              (returned : returnsInteger computation expected = true) :
              computation = .ok (.integer expected) := by
            cases computation <;> simp [returnsInteger] at returned
            rename_i value
            cases value <;> simp_all
          have encodeUpper : (List.range 256).all (fun n => returnsInteger
              (Erlang.erlang.«element/2» (.integer (n+1)) encodeTable) (hexValue false n)) = true := by decide
          have encodeLower : (List.range 256).all (fun n => returnsInteger
              (Erlang.erlang.«element/2» (.integer (n+257)) encodeTable) (hexValue true n)) = true := by decide
          have decodeUpper : (List.range 16).all (fun n => returnsInteger
              (Erlang.erlang.«element/2» (.integer (digit false n)) decodeTable) n) = true := by decide
          have decodeLower : (List.range 16).all (fun n => returnsInteger
              (Erlang.erlang.«element/2» (.integer (digit true n)) decodeTable) n) = true := by decide
          have encodeLookup (lower : Bool) (n : Nat) (bound : n<256) :
              Erlang.erlang.«element/2» (.integer ((n:Int)+offset lower)) encodeTable = .ok (.integer (hexValue lower n)) := by
            cases lower
            · exact returnsInteger_ok _ _ (List.all_eq_true.mp encodeUpper n (List.mem_range.mpr bound))
            · exact returnsInteger_ok _ _ (List.all_eq_true.mp encodeLower n (List.mem_range.mpr bound))
          have decodeLookup (lower : Bool) (n : Nat) (bound : n<16) :
              Erlang.erlang.«element/2» (.integer (digit lower n)) decodeTable = .ok (.integer n) := by
            cases lower
            · exact returnsInteger_ok _ _ (List.all_eq_true.mp decodeUpper n (List.mem_range.mpr bound))
            · exact returnsInteger_ok _ _ (List.all_eq_true.mp decodeLower n (List.mem_range.mpr bound))
          have digitBound (lower : Bool) (n : Nat) (bound : n<16) : digit lower n<256 := by
            cases lower <;> dsimp [digit] <;> split <;> omega
          have modulo (n width : Nat) :
              integerBits (n%2^width : Nat) width false = integerBits n width false := by
            simpa only [decodeInteger_integerBits, integerBits_length] using
              integerBits_decodeInteger (integerBits n width false)
          have join4 (a b : Nat) (bound : b<16) :
              integerBits (a*16+b : Nat) 8 false = integerBits a 4 false ++ integerBits b 4 false := by
            have quotient : (a*16+b)/16=a := by omega
            have remainder : (a*16+b)%16=b := by omega
            have low := modulo (a*16+b) 4
            simp only [show 2^4=16 by decide, remainder] at low
            rw [integerBits_add (a*16+b : Nat) 4 4]
            simp only [←Int.natCast_shiftRight, Nat.shiftRight_eq_div_pow, show 2^4=16 by decide, quotient, ←low]
          have join8 (a b : Nat) (bound : b<256) :
              integerBits (a*256+b : Nat) 16 false = integerBits a 8 false ++ integerBits b 8 false := by
            have quotient : (a*256+b)/256=a := by omega
            have remainder : (a*256+b)%256=b := by omega
            have low := modulo (a*256+b) 8
            simp only [show 2^8=256 by decide, remainder] at low
            rw [integerBits_add (a*256+b : Nat) 8 8]
            simp only [←Int.natCast_shiftRight, Nat.shiftRight_eq_div_pow, show 2^8=256 by decide, quotient, ←low]
          let source (ns : List (Fin 16)) := ns.flatMap (fun n => integerBits n.val 4 false)
          let wire (lower : Bool) (ns : List (Fin 16)) := ns.flatMap (fun n => integerBits (digit lower n.val) 8 false)
          have sourceLength (ns : List (Fin 16)) : (source ns).length=ns.length*4 := by
            induction ns with
            | nil => rfl
            | cons n ns ih => simp only [source, List.flatMap_cons, List.length_append, List.length_cons, integerBits_length] at *; omega
          have wireLength (lower : Bool) (ns : List (Fin 16)) : (wire lower ns).length=ns.length*8 := by
            induction ns with
            | nil => rfl
            | cons n ns ih => simp only [wire, List.flatMap_cons, List.length_append, List.length_cons, integerBits_length] at *; omega
          have tailMatch (bits : List Bool) (unit : Nat) (lo : 1≤unit) (hi : unit≤256)
              (aligned : bits.length%unit=0) : matchTail (ofBits bits) (.atom "all") unit=true := by
            simp [matchTail, ofBits, pack_bitSize, lo, hi, aligned]
          have segment (bits : List Bool) (unit : Nat) (lo : 1≤unit) (hi : unit≤256)
              (aligned : bits.length%unit=0) : binarySegment (ofBits bits) (.atom "all") unit=.ok (ofBits bits) := by
            simp [binarySegment, ofBits, pack_bitSize, lo, hi, aligned]
          have field8 (n : Nat) (tail : List Bool) (bound : n<256) :
              matchInteger (ofBits (integerBits n 8 false++tail)) (.integer 8) 1 false false =
                some (.integer n, ofBits tail) := by
            simpa [integerBits_length, decodeInteger_integerBits, Nat.mod_eq_of_lt bound] using
              matchInteger_prefix (integerBits n 8 false) tail
          have construct4 (n : Int) : integerSegment (.integer n) (.integer 4) 1 false =
              .ok (ofBits (integerBits n 4 false)) := integerSegment_bits n 4
          have construct16 (n : Int) : integerSegment (.integer n) (.integer 16) 1 false =
              .ok (ofBits (integerBits n 16 false)) := integerSegment_bits n 16
          have okBind {α β : Type} (value : α) (next : α → Lynx.Result β) :
              (Lynx.Result.ok value >>= next) = next value := rfl
          have sourceNil : source []=[] := rfl
          have wireNil (lower : Bool) : wire lower []=[] := rfl
          have sourceCons (n : Fin 16) (ns : List (Fin 16)) :
              source (n::ns)=integerBits n.val 4 false++source ns := rfl
          have wireCons (lower : Bool) (n : Fin 16) (ns : List (Fin 16)) :
              wire lower (n::ns)=integerBits (digit lower n.val) 8 false++wire lower ns := rfl
          have sourcePair (a b : Fin 16) (ns : List (Fin 16)) :
              source (a::b::ns)=integerBits (a.val*16+b.val : Nat) 8 false++source ns := by
            rw [sourceCons, sourceCons, ←List.append_assoc, ←join4 a.val b.val b.isLt]
          have encodePair (lower : Bool) (a b : Fin 16) :
              Erlang.erlang.«element/2» (.integer (((a.val*16+b.val:Nat):Int)+offset lower)) encodeTable =
              .ok (.integer (digit lower a.val*256+digit lower b.val : Nat)) := by
            have quotient : (a.val*16+b.val)/16=a.val := by have := b.isLt; omega
            have remainder : (a.val*16+b.val)%16=b.val := by have := b.isLt; omega
            simpa only [hexValue, quotient, remainder] using encodeLookup lower (a.val*16+b.val)
              (by have := a.isLt; have := b.isLt; omega)
          have codePair (lower : Bool) (a b : Fin 16) :
              integerSegment (.integer (digit lower a.val*256+digit lower b.val : Nat)) (.integer 16) 1 false =
              .ok (ofBits (integerBits (digit lower a.val) 8 false++integerBits (digit lower b.val) 8 false)) := by
            rw [construct16, join8 _ _ (digitBound lower b.val b.isLt)]
          have decTail (lower : Bool) (ns : List (Fin 16)) : ∀ acc : List Bool, acc.length%4=0 →
              Erlang.binary.«decode_hex2/2» (ofBits (wire lower ns)) (ofBits acc) =
                .ok (ofBits (acc++source ns)) := by
            induction ns with
            | nil =>
              intro acc aligned
              simp only [wireNil, sourceNil, List.append_nil]
              conv => lhs; unfold Erlang.binary.«decode_hex2/2»
              rfl
            | cons n ns ih =>
              intro acc aligned
              have charBound := digitBound lower n.val n.isLt
              rw [wireCons]
              conv => lhs; unfold Erlang.binary.«decode_hex2/2»
              lynx_fold_table decodeTable
              simp (disch := (try simp only [wireLength]); omega) only
                [field8, extract_some, tailMatch, decodeLookup, okBind, construct4, segment, Lynx.Result.bind, append_bits]
              rw [ih _ (by simp only [List.length_append, integerBits_length]; omega)]
              simp only [sourceCons, List.append_assoc]
          have encTail (lower : Bool) (ns : List (Fin 16)) (even : ns.length%2=0) :
              ∀ acc : List Bool, acc.length%8=0 →
              Erlang.binary.«encode_hex2/3» (ofBits (source ns)) (.integer (offset lower)) (ofBits acc) =
                .ok (ofBits (acc++wire lower ns)) := by
            induction length : ns.length using Nat.strongRecOn generalizing ns with
            | ind size ih =>
              rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩
              · intro acc aligned
                simp only [sourceNil, wireNil, List.append_nil]
                conv => lhs; unfold Erlang.binary.«encode_hex2/3»
                rfl
              · simp at even
              · intro acc aligned
                have restEven : rest.length%2=0 := by simp only [List.length_cons] at even; omega
                have byteBound : a.val*16+b.val<256 := by have := a.isLt; have := b.isLt; omega
                rw [sourcePair]
                conv => lhs; unfold Erlang.binary.«encode_hex2/3»
                lynx_fold_table encodeTable
                simp (disch := (try simp only [sourceLength]); omega) only
                  [field8, extract_some, tailMatch, Erlang.erlang.«+/2_integers», encodePair, okBind,
                   codePair, segment, Lynx.Result.bind, append_bits]
                rw [ih rest.length (by simp only [List.length_cons] at length; omega) rest restEven rfl _
                  (by simp only [List.length_append, integerBits_length]; omega)]
                simp only [wireCons, List.append_assoc]
          have decBlockStep (lower : Bool) (a b c d e f g h : Fin 16) (rest : List (Fin 16)) (acc : List Bool) :
              Erlang.binary.«lynx_local_6/2» (ofBits (wire lower (a::b::c::d::e::f::g::h::rest))) (ofBits acc) =
              Erlang.binary.«lynx_local_6/2» (ofBits (wire lower rest)) (ofBits (acc++source (a::b::c::d::e::f::g::h::[]))) := by
            simp only [wireCons]
            conv => lhs; unfold Erlang.binary.«lynx_local_6/2»
            lynx_fold_table decodeTable
            have ha := a.isLt
            have hb := b.isLt
            have hc := c.isLt
            have hd := d.isLt
            have he := e.isLt
            have hf := f.isLt
            have hg := g.isLt
            have hh := h.isLt
            have ca := digitBound lower a.val ha
            have cb := digitBound lower b.val hb
            have cc := digitBound lower c.val hc
            have cd := digitBound lower d.val hd
            have ce := digitBound lower e.val he
            have cf := digitBound lower f.val hf
            have cg := digitBound lower g.val hg
            have ch := digitBound lower h.val hh
            simp (disch := (try simp only [sourceLength, wireLength]); omega) only
              [field8, extract_some, tailMatch, decodeLookup, okBind, construct4, binarySegment_bits, Lynx.Result.bind, append_bits, sourceCons, sourceNil, List.append_nil, List.append_assoc]
          have decBlockEmpty (lower : Bool) (acc : List Bool) :
              Erlang.binary.«lynx_local_6/2» (ofBits []) (ofBits acc) = .ok (ofBits acc) := by
            conv => lhs; unfold Erlang.binary.«lynx_local_6/2»
            rfl
          have decBlock (lower : Bool) (ns : List (Fin 16)) (blocks : ns.length%8=0) : ∀ acc : List Bool,
              Erlang.binary.«lynx_local_6/2» (ofBits (wire lower ns)) (ofBits acc) =
                .ok (ofBits (acc++source ns)) := by
            induction length : ns.length using Nat.strongRecOn generalizing ns with
            | ind size ih =>
              rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, rest⟩⟩⟩⟩⟩⟩⟩⟩
              all_goals try (simp only [List.length_nil, List.length_cons] at blocks; omega)
              · intro acc
                simpa only [sourceNil, wireNil, List.append_nil] using decBlockEmpty lower acc
              · intro acc
                rw [decBlockStep]
                rw [ih rest.length (by simp only [List.length_cons] at length; omega) rest
                  (by simp only [List.length_cons] at blocks; omega) rfl]
                simp only [sourceCons, sourceNil, List.append_nil, List.append_assoc]
          have encBlockStep (lower : Bool) (a b c d e f g h i j k l m n o p : Fin 16) (rest : List (Fin 16)) (acc : List Bool) :
              Erlang.binary.«lynx_local_2/3» (ofBits (source (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::rest))) (ofBits acc) (.integer (offset lower)) =
              Erlang.binary.«lynx_local_2/3» (ofBits (source rest)) (ofBits (acc++wire lower (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::[]))) (.integer (offset lower)) := by
            simp only [sourcePair]
            conv => lhs; unfold Erlang.binary.«lynx_local_2/3»
            lynx_fold_table encodeTable
            have ha := a.isLt
            have hb := b.isLt
            have hc := c.isLt
            have hd := d.isLt
            have he := e.isLt
            have hf := f.isLt
            have hg := g.isLt
            have hh := h.isLt
            have hi := i.isLt
            have hj := j.isLt
            have hk := k.isLt
            have hl := l.isLt
            have hm := m.isLt
            have hn := n.isLt
            have ho := o.isLt
            have hp := p.isLt
            simp (disch := (try simp only [sourceLength, wireLength]); omega) only
              [field8, extract_some, tailMatch, Erlang.erlang.«+/2_integers», encodePair, okBind, codePair, binarySegment_bits, Lynx.Result.bind, append_bits, wireCons, wireNil, List.append_nil, List.append_assoc]
          have encBlockEmpty (lower : Bool) (acc : List Bool) :
              Erlang.binary.«lynx_local_2/3» (ofBits []) (ofBits acc) (.integer (offset lower)) = .ok (ofBits acc) := by
            conv => lhs; unfold Erlang.binary.«lynx_local_2/3»
            rfl
          have encBlock (lower : Bool) (ns : List (Fin 16)) (blocks : ns.length%16=0) : ∀ acc : List Bool,
              Erlang.binary.«lynx_local_2/3» (ofBits (source ns)) (ofBits acc) (.integer (offset lower)) =
                .ok (ofBits (acc++wire lower ns)) := by
            induction length : ns.length using Nat.strongRecOn generalizing ns with
            | ind size ih =>
              rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨l, _ | ⟨m, _ | ⟨n, _ | ⟨o, _ | ⟨p, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
              all_goals try (simp only [List.length_nil, List.length_cons] at blocks; omega)
              · intro acc
                simpa only [sourceNil, wireNil, List.append_nil] using encBlockEmpty lower acc
              · intro acc
                rw [encBlockStep]
                rw [ih rest.length (by simp only [List.length_cons] at length; omega) rest
                  (by simp only [List.length_cons] at blocks; omega) rfl]
                simp only [wireCons, wireNil, List.append_nil, List.append_assoc]
          have sourceAppend (left right : List (Fin 16)) : source (left++right)=source left++source right := by
            simp only [source, List.flatMap_append]
          have wireAppend (lower : Bool) (left right : List (Fin 16)) :
              wire lower (left++right)=wire lower left++wire lower right := by
            simp only [wire, List.flatMap_append]
          have matchPrefix (head tail : List Bool) (count : Nat) (length : head.length=count*64) :
              matchBinary (ofBits (head++tail)) (.integer count) 64=some (ofBits head, ofBits tail) := by
            simp only [matchBinary, ofBits]
            rw [pack_toBits]
            simp [←length]
          have sourceSize (ns : List (Fin 16)) :
              Erlang.erlang.«bit_size/1» (ofBits (source ns))=.ok (.integer (ns.length*4 : Nat)) := by
            simp only [Erlang.erlang.«bit_size/1», ofBits]
            rw [pack_bitSize, sourceLength]
          have sourceDiv (size : Nat) :
              Erlang.erlang.«div/2» (.integer (size*4 : Nat)) (.integer 64)=.ok (.integer (size/16 : Nat)) := by
            change Lynx.Result.ok (Lynx.Term.integer ((size*4)/64 : Nat))=Lynx.Result.ok (Lynx.Term.integer (size/16 : Nat))
            rw [show (size*4)/64=size/16 by omega]
          have wireSize (lower : Bool) (ns : List (Fin 16)) :
              Erlang.erlang.«byte_size/1» (ofBits (wire lower ns))=.ok (.integer ns.length) := by
            simp only [Erlang.erlang.«byte_size/1», ofBits, pack_size, wireLength]
            rw [show (ns.length*8+7)/8=ns.length by omega]
          have wireDiv (size : Nat) :
              Erlang.erlang.«div/2» (.integer size) (.integer 8)=.ok (.integer (size/8 : Nat)) := by rfl
          have encodeFull (lower : Bool) (ns : List (Fin 16)) (even : ns.length%2=0) :
              Erlang.binary.«encode_hex1/2» (ofBits (source ns)) (.integer (offset lower)) =
                .ok (ofBits (wire lower ns)) := by
            let count := ns.length/16
            let first := ns.take (count*16)
            let rest := ns.drop (count*16)
            have enough : count*16≤ns.length := by dsimp [count]; omega
            have firstLength : first.length=count*16 := List.length_take_of_le enough
            have restLength : rest.length=ns.length-count*16 := List.length_drop
            have joined : first++rest=ns := List.take_append_drop _ _
            have represented : source ns=source first++source rest := by rw [←joined, sourceAppend]
            have prefixSize : (source first).length=count*64 := by rw [sourceLength, firstLength]; omega
            have restAligned : (source rest).length%8=0 := by rw [sourceLength]; omega
            conv => lhs; unfold Erlang.binary.«encode_hex1/2»
            simp only [matchTail_bits, sourceSize, sourceDiv, Lynx.Result.tryWith_ok, okBind, pure_bind]
            rw [represented]
            rw [matchPrefix _ _ count prefixSize]
            simp only [extract_some, tailMatch _ 8 (by decide) (by decide) restAligned, pure_bind]
            change (Erlang.binary.«lynx_local_2/3» (ofBits (source first)) (ofBits []) (.integer (offset lower)) >>=
              fun value => Erlang.binary.«encode_hex2/3» (ofBits (source rest)) (.integer (offset lower)) value) = _
            rw [encBlock lower first (by omega) []]
            simp only [okBind, List.nil_append]
            rw [encTail lower rest (by omega) _ (by rw [wireLength]; omega)]
            simp only [List.nil_append, ←wireAppend, joined]
          have decodeFull (lower : Bool) (ns : List (Fin 16)) :
              Erlang.binary.«decode_hex1/1» (ofBits (wire lower ns)) = .ok (ofBits (source ns)) := by
            let count := ns.length/8
            let first := ns.take (count*8)
            let rest := ns.drop (count*8)
            have enough : count*8≤ns.length := by dsimp [count]; omega
            have firstLength : first.length=count*8 := List.length_take_of_le enough
            have joined : first++rest=ns := List.take_append_drop _ _
            have represented : wire lower ns=wire lower first++wire lower rest := by rw [←joined, wireAppend]
            have prefixSize : (wire lower first).length=count*64 := by rw [wireLength, firstLength]; omega
            have restAligned : (wire lower rest).length%8=0 := by rw [wireLength]; omega
            conv => lhs; unfold Erlang.binary.«decode_hex1/1»
            simp only [matchTail_bits, wireSize, wireDiv, Lynx.Result.tryWith_ok, okBind, pure_bind]
            rw [represented]
            rw [matchPrefix _ _ count prefixSize]
            simp only [extract_some, tailMatch _ 8 (by decide) (by decide) restAligned, pure_bind]
            change (Erlang.binary.«lynx_local_6/2» (ofBits (wire lower first)) (ofBits []) >>=
              fun value => Erlang.binary.«decode_hex2/2» (ofBits (wire lower rest)) value) = _
            rw [decBlock lower first (by omega) []]
            simp only [okBind, List.nil_append]
            rw [decTail lower rest _ (by rw [sourceLength]; omega)]
            simp only [List.nil_append, ←sourceAppend, joined]
          have binaryBits (bits : List Bool) (aligned : bits.length%8=0) :
              ofBits bits=.bitstring (pack bits) 0 (valid_aligned _) := by
            have last : (⟨bits.length%8, Nat.mod_lt _ (by decide)⟩ : Fin 8)=0 := Fin.ext aligned
            simp only [ofBits]
            congr 1
          have encodePublic (lower : Bool) (ns : List (Fin 16)) (even : ns.length%2=0) :
              Erlang.binary.«encode_hex/2» (ofBits (source ns))
                (.atom (if lower then "lowercase" else "uppercase"))=.ok (ofBits (wire lower ns)) := by
            have aligned : (source ns).length%8=0 := by rw [sourceLength]; omega
            have encoded := encodeFull lower ns even
            rw [binaryBits _ aligned] at encoded ⊢
            cases lower <;> simpa [Erlang.binary.«encode_hex/2», offset] using encoded
          have decodePublic (lower : Bool) (ns : List (Fin 16)) (even : ns.length%2=0) :
              Erlang.binary.«decode_hex/1» (ofBits (wire lower ns))=.ok (ofBits (source ns)) := by
            have remainder : Erlang.erlang.«rem/2» (.integer ns.length) (.integer 2)=.ok (.integer 0) := by
              change Lynx.Result.ok (Lynx.Term.integer (ns.length%2 : Nat))=Lynx.Result.ok (Lynx.Term.integer 0)
              rw [even]; rfl
            unfold Erlang.binary.«decode_hex/1»
            simp [wireSize, remainder, Erlang.erlang.«=:=/2», Lynx.Result.guard, decodeFull]
          have nibbleModel (bits : List Bool) (aligned : bits.length%4=0) :
              ∃ ns : List (Fin 16), source ns=bits := by
            induction length : bits.length using Nat.strongRecOn generalizing bits with
            | ind size ih =>
              by_cases empty : size=0
              · have emptyBits : bits=[] := List.eq_nil_of_length_eq_zero (by omega)
                exact ⟨[], by simpa only [sourceNil] using emptyBits.symm⟩
              · have enough : 4≤bits.length := by omega
                have bound : decodeInteger (bits.take 4) false<16 := by
                  simpa only [List.length_take_of_le enough, show 2^4=16 by decide] using decodeInteger_lt (bits.take 4)
                obtain ⟨ns, represented⟩ := ih (bits.drop 4).length
                  (by simp only [List.length_drop]; omega) (bits.drop 4)
                  (by simp only [List.length_drop]; omega) rfl
                refine ⟨⟨decodeInteger (bits.take 4) false, bound⟩::ns, ?_⟩
                rw [sourceCons, represented]
                have inverse : integerBits (decodeInteger (bits.take 4) false) 4 false=bits.take 4 := by
                  simpa only [List.length_take_of_le enough] using integerBits_decodeInteger (bits.take 4)
                rw [inverse, List.take_append_drop]
          cases bytes <;> try (simp [«hex_roundtrip:requires/2», Erlang.erlang.«is_binary/1»] at requires)
          rename_i storage last valid
          rcases last with ⟨last,lastLt⟩
          cases last with
          | succ last => simp [«hex_roundtrip:requires/2», Erlang.erlang.«is_binary/1»] at requires
          | zero =>
            change «hex_roundtrip:ensures/2» (.bitstring storage 0 valid) mode=.ok Lynx.Term.true
            have modeCases : mode=.atom "uppercase" ∨ mode=.atom "lowercase" := by
              by_cases upper : mode=.atom "uppercase"
              · exact Or.inl upper
              · right
                apply Classical.byContradiction
                intro lower
                simp [«hex_roundtrip:requires/2», Erlang.erlang.«is_binary/1», Erlang.erlang.«=:=/2»,
                  upper, lower] at requires
            obtain ⟨lower, rfl⟩ : ∃ lower : Bool, mode=.atom (if lower then "lowercase" else "uppercase") := by
              rcases modeCases with upper | lower
              · exact ⟨false,upper⟩
              · exact ⟨true,lower⟩
            have bitLength : (toBits storage 0).length=storage.size*8 := toBits_length_aligned storage
            obtain ⟨ns,represented⟩ := nibbleModel (toBits storage 0) (by omega)
            have nsLength : ns.length=storage.size*2 := by
              have lengths := congrArg List.length represented
              rw [sourceLength,bitLength] at lengths
              omega
            have original : ofBits (source ns)=.bitstring storage 0 valid := by
              rw [represented]
              exact ofBits_toBits_aligned storage
            have encoded := encodePublic lower ns (by omega)
            rw [original] at encoded
            have decoded := decodePublic lower ns (by omega)
            rw [original] at decoded
            simp only [«hex_roundtrip:ensures/2», «hex_contract/2»]
            rw [encoded]
            simp only [okBind,decoded]
            simp only [Erlang.erlang.«=:=/2», Lynx.Term.exactCompare_self, if_true, Lynx.Term.true, okBind]
            rw [wireSize]
            simp [Erlang.erlang.«=:=/2», Lynx.Term.true,
              Erlang.erlang.«byte_size/1», Erlang.erlang.«*/2_integers», nsLength,
              Int.natCast_mul, Int.mul_comm]
      """
  end
end
