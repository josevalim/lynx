module

public import Lynx.Term

public section

/-! Portable term hashing, following `make_hash2` in OTP's `erl_term_hashing.c`.

Hashes of integers, floats, atoms, bitstrings, lists, tuples, and maps match
the BEAM on 64-bit platforms. The BEAM hashes PIDs, references, and functions
by runtime identifiers that Lynx does not model, so their hashes are
unspecified: proofs may only rely on them being deterministic and in range. -/

namespace Erlang.erlang

open Lynx

/-- Bob Jenkins' mixing function, as `MIX` in OTP. -/
private def mix (a b c : UInt32) : UInt32 × UInt32 × UInt32 :=
  let a := a - b - c
  let a := a ^^^ (c >>> 13)
  let b := b - c - a
  let b := b ^^^ (a <<< 8)
  let c := c - a - b
  let c := c ^^^ (b >>> 13)
  let a := a - b - c
  let a := a ^^^ (c >>> 12)
  let b := b - c - a
  let b := b ^^^ (a <<< 16)
  let c := c - a - b
  let c := c ^^^ (b >>> 5)
  let a := a - b - c
  let a := a ^^^ (c >>> 3)
  let b := b - c - a
  let b := b ^^^ (a <<< 10)
  let c := c - a - b
  let c := c ^^^ (b >>> 15)
  (a, b, c)

/-- `HCONST * n`, the golden ratio multiples OTP uses to separate term kinds. -/
private def hconst (n : UInt32) : UInt32 := 0x9e3779b9 * n

/-- `UINT32_HASH_2`, mixing two words into the running hash. -/
private def hashWords (x y constant hash : UInt32) : UInt32 :=
  (mix (constant + x) (constant + y) hash).2.2

/-- `UINT32_HASH`. -/
private def hashWord (x constant hash : UInt32) : UInt32 :=
  hashWords x 0 constant hash

private def wrap (value : Int) : UInt32 := UInt32.ofNat (value % 2 ^ 32).toNat

/-- Integers in `[-2^27, 2^27)` are mixed as signed words; negative ones twice.
Larger magnitudes are mixed in 64-bit digits, least significant first, which
matches both large immediates and bignums. -/
private def hashInteger (value : Int) (hash : UInt32) : UInt32 :=
  if -2 ^ 27 ≤ value ∧ value < 2 ^ 27 then
    let hash := if value < 0 then hashWord (wrap (-value)) (hconst 1) hash else hash
    hashWord (wrap value) (hconst 1) hash
  else
    let constant := if value < 0 then hconst 10 else hconst 11
    let rec digits (magnitude : Nat) (hash : UInt32) : UInt32 :=
      let hash := hashWords (UInt32.ofNat magnitude) (UInt32.ofNat (magnitude / 2 ^ 32))
        constant hash
      if magnitude < 2 ^ 64 then hash else digits (magnitude / 2 ^ 64) hash
    termination_by magnitude
    decreasing_by omega
    digits value.natAbs hash

/-- The positive zero replaces negative zero before mixing the IEEE words. -/
private def hashFloat (value : Term.FiniteFloat) (hash : UInt32) : UInt32 :=
  let bits :=
    if value.exponent.val = 0 ∧ value.fraction.val = 0 then 0
    else (if value.negative then 2 ^ 63 else 0) + value.exponent.val * 2 ^ 52 + value.fraction.val
  hashWords (UInt32.ofNat (bits / 2 ^ 32)) (UInt32.ofNat bits) (hconst 12) hash

/-- The atom table's hashpjw over the UTF-8 name, in a 64-bit word. Two-byte
sequences for Latin-1 characters are folded into their code point. -/
private def atomTableHash (name : String) : UInt32 :=
  let step (h : UInt64) (v : UInt8) : UInt64 :=
    let h := (h <<< 4) + v.toUInt64
    let g := h &&& 0xf0000000
    if g = 0 then h else h ^^^ (g >>> 24) ^^^ g
  let rec go (h : UInt64) : List UInt8 → UInt64
    | [] => h
    | v :: next :: rest =>
      if v &&& 0xFE = 0xC2 ∧ next &&& 0xC0 = 0x80 then go (step h ((v <<< 6) ||| (next &&& 0x3F))) rest
      else go (step h v) (next :: rest)
    | [v] => step h v
  (go 0 name.toUTF8.toList).toUInt32

/-- The leading atom or `[]` of a hash takes its table value without mixing. -/
private def hashAtom (name : String) (hash : UInt32) : UInt32 :=
  if hash = 0 then atomTableHash name else hashWord (atomTableHash name) (hconst 3) hash

private def hashNil (hash : UInt32) : UInt32 :=
  if hash = 0 then 3468870702 else hashWord 2 (hconst 2) hash

private def word (bytes : ByteArray) (offset : Nat) : UInt32 :=
  bytes[offset]!.toUInt32 ||| (bytes[offset + 1]!.toUInt32 <<< 8) |||
    (bytes[offset + 2]!.toUInt32 <<< 16) ||| (bytes[offset + 3]!.toUInt32 <<< 24)

/-- Jenkins' lookup2 over the first `length` bytes, as `block_hash` in OTP. -/
private def blockHash (bytes : ByteArray) (length : Nat) (initial : UInt32) : UInt32 :=
  let rec blocks (offset : Nat) (a b c : UInt32) : UInt32 :=
    if offset + 12 ≤ length then
      let (a, b, c) := mix (a + word bytes offset) (b + word bytes (offset + 4))
        (c + word bytes (offset + 8))
      blocks (offset + 12) a b c
    else
      let byte (index : Nat) (shift : UInt32) : UInt32 :=
        if offset + index < length then bytes[offset + index]!.toUInt32 <<< shift else 0
      let a := a + byte 0 0 + byte 1 8 + byte 2 16 + byte 3 24
      let b := b + byte 4 0 + byte 5 8 + byte 6 16 + byte 7 24
      -- The first byte of `c` is reserved for the length.
      let c := c + UInt32.ofNat length + byte 8 8 + byte 9 16 + byte 10 24
      (mix a b c).2.2
  termination_by length - offset
  blocks 0 0x9e3779b9 0x9e3779b9 initial

/-- Whole bytes go through the block hash, then any trailing bits with their count. -/
private def hashBitstring (bytes : ByteArray) (lastBits : Fin 8) (hash : UInt32) : UInt32 :=
  let whole := if lastBits = 0 then bytes.size else bytes.size - 1
  let constant := hconst 13 + hash
  if bytes.size = 0 then constant
  else
    let hash := blockHash bytes whole constant
    if lastBits = 0 then hash
    else hashWords lastBits.val.toUInt32 (bytes[whole]! >>> (8 - lastBits.val.toUInt8)).toUInt32
      (hconst 15) hash

/-- Runtime identities the BEAM hashes but Lynx does not model. -/
private opaque hashIdentity (term : Term) (hash : UInt32) : UInt32

private def byte? : Term → Option UInt32
  | .integer value => if 0 ≤ value ∧ value < 256 then some (wrap value) else none
  | _ => none

private theorem sizeOf_pos (term : Term) : 0 < sizeOf term := by
  cases term <;> simp <;> omega

/-- Visible bindings are smaller than their map. -/
private theorem visible_lt {entries : List (Term × Term)} {entry : Term × Term}
    (h : entry ∈ Term.Compare.mapView Term.exactCompare entries) :
    sizeOf entry.1 < 1 + sizeOf entries ∧ sizeOf entry.2 < 1 + sizeOf entries := by
  have := List.sizeOf_lt_of_mem (Term.Compare.mem_mapView _ h)
  obtain ⟨k, v⟩ := entry
  simp only [Prod.mk.sizeOf_spec] at this ⊢
  omega

mutual

/-- Hash a term into the running hash, in `make_hash2`'s traversal order. -/
private def hashTerm (hash : UInt32) : Term → UInt32
  | .integer value => hashInteger value hash
  | .float value => hashFloat value hash
  | .atom name => hashAtom name hash
  | .nil => hashNil hash
  | .cons head tail => hashList hash 0 0 head tail
  | .tuple elements =>
    elements.attach.foldl (fun hash element => hashTerm hash element.val)
      (hashWord (UInt32.ofNat elements.size) (hconst 9) hash)
  | .map entries =>
    -- The visible bindings, which exact equality compares, each hashed independently.
    let view := (Term.Compare.mapView Term.exactCompare entries).attach
    let pairs := view.foldl (fun pairs entry => pairs ^^^ hashTerm (hashTerm 0 entry.val.1) entry.val.2) 0
    let hash := hashWord (UInt32.ofNat view.length) (hconst 16) hash
    if view.length = 0 then hash else hashWord pairs (hconst 19) hash
  | .bitstring bytes lastBits _ => hashBitstring bytes lastBits hash
  -- Functions hash their captures as the BEAM does, after their unmodeled identity.
  | .function module name arity captures =>
    captures.attach.foldl (fun hash capture => hashTerm hash capture.val)
      (hashIdentity (.function module name arity #[]) hash)
  | term@(.pid _) | term@(.reference _) => hashIdentity term hash
termination_by term => sizeOf term
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem element.property; simp_all; try omega)
    | (have := Array.sizeOf_lt_of_mem capture.property; simp_all; try omega)
    | (have := visible_lt entry.property; simp only [Term.map.sizeOf_spec]; omega)
    | (simp_all; try omega)

/-- Byte elements are packed four at a time, as strings are. The run ends at
an improper tail, which is hashed next, or at another element, which is hashed
before the rest of the list. -/
private def hashList (hash packed : UInt32) (count : Nat) (head tail : Term) : UInt32 :=
  let flush (hash : UInt32) := if count > 0 then hashWord packed (hconst 4) hash else hash
  match byte? head with
  | some value =>
    let packed := (packed <<< 8) + value
    let (hash, packed, count) :=
      if count = 3 then (hashWord packed (hconst 4) hash, 0, 0) else (hash, packed, count + 1)
    match tail with
    | .cons head tail => hashList hash packed count head tail
    | tail => hashTerm (if count > 0 then hashWord packed (hconst 4) hash else hash) tail
  | none => hashTerm (hashTerm (flush hash) head) tail
termination_by sizeOf head + sizeOf tail
decreasing_by all_goals (have := sizeOf_pos head; have := sizeOf_pos tail; simp_all; try omega)

end

/-- The full 32-bit portable hash of a term. -/
private def hash2 (term : Term) : UInt32 := hashTerm 0 term

/-- `erlang:phash2/1`: the portable hash in `[0, 2^27)`. -/
def «phash2/1» (term : Term) : Except Exception Term :=
  .ok (.integer (hash2 term &&& (2 ^ 27 - 1)).toNat)

/-- `erlang:phash2/2`: the portable hash in `[0, Range)`, for `Range` in `[1, 2^32]`. -/
def «phash2/2» (term range : Term) : Except Exception Term :=
  match range with
  | .integer (.ofNat (n + 1)) =>
    if n + 1 ≤ 2 ^ 32 then .ok (.integer ((hash2 term).toNat % (n + 1))) else .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

/-- `phash2/1` always returns an integer in `[0, 2^27)`. -/
theorem phash2_range (term : Term) :
    ∃ hash : Nat, «phash2/1» term = .ok (.integer hash) ∧ hash < 2 ^ 27 :=
  ⟨_, rfl, Nat.lt_of_le_of_lt (by simpa using Nat.and_le_right) (by decide)⟩

/-! Exactly equal terms hash equally. -/

/-- Lists related element by element. -/
private inductive Pairwise₂ (R : Term → Term → Prop) : List Term → List Term → Prop
  | nil : Pairwise₂ R [] []
  | cons {x y xs ys} : R x y → Pairwise₂ R xs ys → Pairwise₂ R (x :: xs) (y :: ys)

private theorem exact_symm {a b : Term} (h : Term.exactCompare a b = .eq) : Term.exactCompare b a = .eq := by
  rw [Std.OrientedCmp.eq_swap (cmp := Term.exactCompare), h]; rfl

private theorem lex_eq {cmp : Term → Term → Ordering} :
    ∀ {xs ys : List Term}, List.compareLex cmp xs ys = .eq → Pairwise₂ (fun a b => cmp a b = .eq) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [List.compareLex_nil_cons] at h
  | _ :: _, [], h => by simp [List.compareLex_cons_nil] at h
  | x :: xs, y :: ys, h => by
    simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
    exact .cons h.1 (lex_eq h.2)

private theorem byte_congr {a b : Term} (h : Term.exactCompare a b = .eq) : byte? a = byte? b := by
  cases a with
  | integer v => rw [Term.integer_exactCompare_eq] at h; subst h; rfl
  | _ =>
    cases b with
    | integer v => rw [Term.exactCompare_eq_integer] at h; cases h
    | _ => rfl

/-- Mapping equal hashes over exactly equal visible bindings. -/
private theorem pairs_congr (g : Term × Term → UInt32) :
    ∀ {xs ys : List (Term × Term)}, Pairwise₂ (fun a b => Term.exactCompare a b = .eq) (xs.map Prod.fst) (ys.map Prod.fst) →
      Pairwise₂ (fun a b => Term.exactCompare a b = .eq) (xs.map Prod.snd) (ys.map Prod.snd) →
      (∀ x ∈ xs, ∀ y, Term.exactCompare x.1 y.1 = .eq → Term.exactCompare x.2 y.2 = .eq → g x = g y) →
      xs.map g = ys.map g
  | [], [], _, _, _ => rfl
  | x :: xs, y :: ys, .cons hk keys, .cons hv values, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h x List.mem_cons_self y hk hv,
      pairs_congr g keys values fun x' m => h x' (List.mem_cons_of_mem _ m)⟩

/-- Folding equal hashes over exactly equal elements. -/
private theorem fold_congr (f : UInt32 → Term → UInt32) :
    ∀ {xs ys : List Term}, Pairwise₂ (fun a b => ∀ h, f h a = f h b) xs ys →
      ∀ h, xs.foldl f h = ys.foldl f h
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons hxy rest, h => by
    simp only [List.foldl_cons, hxy h]
    exact fold_congr f rest _

private theorem forall₂_mem {R : Term → Term → Prop} :
    ∀ {xs ys : List Term}, Pairwise₂ R xs ys → Pairwise₂ (fun a b => a ∈ xs ∧ R a b) xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h rest =>
    .cons ⟨List.mem_cons_self, h⟩ (mono (forall₂_mem rest) fun _ _ ⟨m, r⟩ => ⟨List.mem_cons_of_mem _ m, r⟩)
where
  mono {R S : Term → Term → Prop} : ∀ {xs ys}, Pairwise₂ R xs ys → (∀ a b, R a b → S a b) → Pairwise₂ S xs ys
    | [], [], .nil, _ => .nil
    | _ :: _, _ :: _, .cons h rest, f => .cons (f _ _ h) (mono rest f)

private theorem hash_congr : ∀ (n : Nat),
    (∀ a b, sizeOf a ≤ n → Term.exactCompare a b = .eq → ∀ hash, hashTerm hash a = hashTerm hash b) ∧
    (∀ head tail head' tail' hash packed count, sizeOf head + sizeOf tail ≤ n →
      Term.exactCompare head head' = .eq → Term.exactCompare tail tail' = .eq →
      hashList hash packed count head tail = hashList hash packed count head' tail') := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  have term : ∀ {a b : Term}, sizeOf a < n → Term.exactCompare a b = .eq →
      ∀ hash, hashTerm hash a = hashTerm hash b :=
    fun {a b} ha h hash => (ih (sizeOf a) ha).1 a b (Nat.le_refl _) h hash
  have elems : ∀ {xs ys : List Term}, (∀ x ∈ xs, sizeOf x < n) →
      List.compareLex Term.exactCompare xs ys = .eq → ∀ hash,
        xs.foldl hashTerm hash = ys.foldl hashTerm hash := by
    intro xs ys small h hash
    exact fold_congr hashTerm (forall₂_mem.mono (forall₂_mem (lex_eq h))
      fun a b ⟨m, e⟩ => term (small a m) e) hash
  constructor
  · intro a b ha h hash
    cases a with
    | integer v => rw [Term.integer_exactCompare_eq] at h; subst h; rfl
    | float v => rw [Term.float_exactCompare_eq] at h; subst h; rfl
    | atom name => have := exact_symm h; rw [Term.exactCompare_eq_atom] at this; subst this; rfl
    | reference r => rw [Term.reference_exactCompare_eq] at h; subst h; rfl
    | pid p =>
      cases b <;> rw [Term.exactCompare_eq_step] at h <;> simp [Term.Compare.compareStep] at h
      subst h; rfl
    | nil => have := exact_symm h; rw [Term.exactCompare_eq_nil] at this; subst this; rfl
    | cons hd tl =>
      obtain ⟨hd', tl', rfl⟩ := Term.cons_exactCompare_eq hd tl b h
      rw [Term.exactCompare_eq_step] at h
      simp only [Term.Compare.compareStep, Ordering.then_eq_eq] at h
      simp only [hashTerm]
      exact (ih (sizeOf hd + sizeOf tl) (by simp at ha; omega)).2 hd tl hd' tl' hash 0 0 (Nat.le_refl _) h.1 h.2
    | tuple xs =>
      cases b <;> rw [Term.exactCompare_eq_step] at h <;> simp [Term.Compare.compareStep] at h
      rename_i ys
      obtain ⟨size, lex⟩ := h
      have small : ∀ x ∈ xs.toList, sizeOf x < n := fun x m => by
        have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp m); simp at ha; omega
      rcases xs with ⟨xs⟩
      rcases ys with ⟨ys⟩
      simp only [List.size_toArray] at size
      simp only [hashTerm, Array.foldl_attach, List.foldl_toArray', List.size_toArray, size]
      exact elems small lex _
    | function m nm ar caps =>
      cases b <;> rw [Term.exactCompare_eq_step] at h <;> simp [Term.Compare.compareStep, Ordering.then_eq_eq] at h
      obtain ⟨rfl, rfl, rfl, lex⟩ := h
      simp only [hashTerm, Array.foldl_attach]
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      exact elems (fun x m => by
        have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp m); simp at ha; omega) lex _
    | map A =>
      cases b <;> rw [Term.exactCompare_eq_step] at h <;> simp [Term.Compare.compareStep] at h
      rename_i B
      simp only [Term.Compare.compareMapViews, compareLex, Term.Compare.compareOn, Ordering.then_eq_eq] at h
      obtain ⟨length, keys, values⟩ := h
      have length : (Term.Compare.mapView Term.exactCompare A).length =
          (Term.Compare.mapView Term.exactCompare B).length := Nat.compare_eq_eq.mp length
      have same := pairs_congr (fun e => hashTerm (hashTerm 0 e.1) e.2) (lex_eq keys) (lex_eq values)
        fun x mx y hk hv => by
          have small := visible_lt mx
          simp only [Term.map.sizeOf_spec] at ha
          rw [term (by omega) hk 0, term (by omega) hv]
      simp only [hashTerm, List.length_attach, length]
      rw [List.foldl_attach (f := fun pairs (entry : Term × Term) => pairs ^^^ hashTerm (hashTerm 0 entry.1) entry.2),
        List.foldl_attach (f := fun pairs (entry : Term × Term) => pairs ^^^ hashTerm (hashTerm 0 entry.1) entry.2)]
      have fold : ∀ xs : List (Term × Term), xs.foldl (fun pairs entry => pairs ^^^ hashTerm (hashTerm 0 entry.1) entry.2) 0 =
          (xs.map fun entry => hashTerm (hashTerm 0 entry.1) entry.2).foldl (fun pairs value => pairs ^^^ value) 0 :=
        fun xs => by rw [List.foldl_map]
      rw [fold, fold, same]
    | bitstring bytes lb v =>
      obtain ⟨other, ob, ov, rfl⟩ := Term.bitstring_exactCompare_eq bytes lb v b h
      rw [Term.exactCompare_eq_step] at h
      simp only [Term.Compare.compareStep] at h
      obtain ⟨rfl, rfl⟩ := Term.Bitstring.eq_of_toBits_eq v ov (Std.LawfulEqCmp.eq_of_compare h)
      rfl
  · intro head tail head' tail' hash packed count hs hh ht
    have hpos := sizeOf_pos head
    have tpos := sizeOf_pos tail
    rw [hashList, hashList, byte_congr hh]
    split
    · rename_i value _
      simp only []
      generalize (if count = 3 then (hashWord (packed <<< 8 + value) (hconst 4) hash, (0 : UInt32), 0)
        else (hash, packed <<< 8 + value, count + 1)) = state
      obtain ⟨hash₂, packed₂, count₂⟩ := state
      simp only []
      by_cases tc : ∃ next rest, tail = .cons next rest
      · obtain ⟨next, rest, rfl⟩ := tc
        obtain ⟨next', rest', rfl⟩ := Term.cons_exactCompare_eq next rest tail' ht
        rw [Term.exactCompare_eq_step] at ht
        simp only [Term.Compare.compareStep, Ordering.then_eq_eq] at ht
        exact (ih (sizeOf next + sizeOf rest) (by simp at hs; omega)).2 _ _ _ _ _ _ _ (Nat.le_refl _) ht.1 ht.2
      · -- The other tail is not a list cell either.
        have _ : ∀ next rest, tail' ≠ .cons next rest := by
          rintro next rest rfl
          obtain ⟨a, b, rfl⟩ := Term.cons_exactCompare_eq next rest tail (exact_symm ht)
          exact tc ⟨a, b, rfl⟩
        split
        · exfalso; exact tc ⟨_, _, rfl⟩
        · generalize (if count₂ > 0 then hashWord packed₂ (hconst 4) hash₂ else hash₂) = hash₃
          exact term (by omega) ht _
    · rw [term (by omega) hh, term (by omega) ht]

theorem phash2_congr {a b : Term} (h : Term.exactCompare a b = .eq) : «phash2/1» a = «phash2/1» b := by
  simp only [«phash2/1», hash2, (hash_congr _).1 a b (Nat.le_refl _) h 0]

end Erlang.erlang
