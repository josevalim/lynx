module

public import Lynx.Term

public section

namespace Erlang.binary
open Lynx

/-- The bytes of a binary. Bitstrings with trailing bits are not binaries. -/
private def bytes? : Term → Option (List UInt8)
  | .bitstring bytes 0 _ => some bytes.data.toList
  | _ => none

private def properList? : Term → Option (List Term)
  | .nil => some []
  | .cons head tail => (properList? tail).map (head :: ·)
  | _ => none

private def binary (bytes : List UInt8) : Term :=
  .bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _)

/-- A nonempty binary, or a nonempty list of them. -/
private def patterns? (pattern : Term) : Option (List (List UInt8)) :=
  match pattern with
  | .cons _ _ =>
    (properList? pattern).bind fun elements =>
      elements.mapM fun element =>
        match bytes? element with
        | some (byte :: rest) => some (byte :: rest)
        | _ => none
  | _ =>
    match bytes? pattern with
    | some (byte :: rest) => some [byte :: rest]
    | _ => none

/-- The bytes `[start, stop)` that a `{Start, Length}` part denotes, where a
negative length extends backwards from the start. -/
private def scope? (size : Nat) : Term → Option (Nat × Nat)
  | .tuple ⟨[.integer start, .integer length]⟩ =>
    let stop := start + length
    let low := min start stop
    let high := max start stop
    if 0 ≤ low ∧ high ≤ size then some (low.toNat, high.toNat) else none
  | _ => none

/-- The length of the longest pattern that the bytes start with, within `limit` bytes. -/
private def longest (patterns : List (List UInt8)) (bytes : List UInt8) (limit : Nat) :
    Option Nat :=
  patterns.foldl (fun best pattern =>
    if pattern.length ≤ limit ∧ pattern.isPrefixOf bytes then
      match best with
      | some length => some (max length pattern.length)
      | none => some pattern.length
    else best) none

/-- The leftmost match within `[low, high)` of the bytes from `offset` on, as an
absolute position and length. -/
private def find (patterns : List (List UInt8)) (low high : Nat) :
    List UInt8 → Nat → Option (Nat × Nat)
  | [], _ => none
  | bytes@(_ :: rest), offset =>
    if high ≤ offset then none
    else if offset < low then find patterns low high rest (offset + 1)
    else match longest patterns bytes (high - offset) with
      | some length => some (offset, length)
      | none => find patterns low high rest (offset + 1)

/-- The parts between matches. `fuel` bounds the number of matches, as each
match consumes at least one byte. -/
private def parts (patterns : List (List UInt8)) (low high : Nat) (global : Bool) :
    Nat → List UInt8 → Nat → List (List UInt8)
  | 0, bytes, _ => [bytes]
  | fuel + 1, bytes, offset =>
    match find patterns low high bytes offset with
    | none => [bytes]
    | some (position, length) =>
      let part := bytes.take (position - offset)
      let rest := bytes.drop (position - offset + length)
      if global then part :: parts patterns low high global fuel rest (position + length)
      else [part, rest]

private structure SplitOptions where
  scope : Option Term := none
  global : Bool := false
  trim : Bool := false
  trimAll : Bool := false

private def splitOptions? : List Term → Option SplitOptions
  | [] => some {}
  | option :: rest => (splitOptions? rest).bind fun options =>
    match option with
    | .atom "global" => some { options with global := true }
    | .atom "trim" => some { options with trim := true }
    | .atom "trim_all" => some { options with trimAll := true }
    | .tuple ⟨[.atom "scope", part]⟩ => some { options with scope := options.scope <|> some part }
    | _ => none

/-- Patterns from `compile_pattern/1` are not modeled, so searches with them do not return. -/
private def unsupported (pattern : Term) : Except Exception Term :=
  match pattern with
  | .tuple ⟨[.atom "bm", .reference _]⟩ | .tuple ⟨[.atom "ac", .reference _]⟩ => .error .exhausted
  | _ => .error (.error (.atom "badarg"))

private def badarg : Except Exception Term := .error (.error (.atom "badarg"))

/-- Split a binary at the occurrences of a pattern, the first one by default
and all of them with `global`. `trim` removes trailing empty parts, and
`trim_all` removes every empty part. A `{scope, Part}` restricts matches to
`Part`, and a later scope replaces an earlier one. -/
def «split/3» (subject pattern options : Term) : Except Exception Term :=
  match bytes? subject, patterns? pattern, (properList? options).bind splitOptions? with
  | some bytes, some patterns, some options =>
    let range := match options.scope with
      | none => some (0, bytes.length)
      | some part => scope? bytes.length part
    match range with
    | some (low, high) =>
      let split := parts patterns low high options.global bytes.length bytes 0
      let split :=
        if options.trimAll then split.filter (· ≠ [])
        else if options.trim then (split.reverse.dropWhile (· = [])).reverse
        else split
      .ok (Term.list (split.map binary))
    | none => badarg
  | _, _, _ => unsupported pattern

def «split/2» (subject pattern : Term) : Except Exception Term :=
  «split/3» subject pattern .nil

/-- The position and length of the leftmost match, preferring the longest
pattern at that position, or `nomatch`. A `{scope, Part}` restricts matches
to `Part`, and a later scope replaces an earlier one. -/
def «match/3» (subject pattern options : Term) : Except Exception Term :=
  match bytes? subject, patterns? pattern, properList? options with
  | some bytes, some patterns, some options =>
    let range := options.foldl (fun range option => range.bind fun _ =>
      match option with
      | .tuple ⟨[.atom "scope", part]⟩ => scope? bytes.length part
      | _ => none) (some (0, bytes.length))
    match range with
    | some (low, high) =>
      match find patterns low high bytes 0 with
      | some (position, length) => .ok (.tuple #[.integer position, .integer length])
      | none => .ok (.atom "nomatch")
    | none => badarg
  | _, _, _ => unsupported pattern

def «match/2» (subject pattern : Term) : Except Exception Term :=
  «match/3» subject pattern .nil

def «last/1» (subject : Term) : Except Exception Term :=
  match bytes? subject with
  | some bytes =>
    match bytes.getLast? with
    | some byte => .ok (.integer byte.toNat)
    | none => badarg
  | none => badarg

end Erlang.binary

namespace Erlang.binary
open Lynx

private theorem binary_eq :
    binary = fun bytes => .bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _) := rfl

private theorem bytes?_binary (bytes : List UInt8) :
    bytes? (.bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _)) = some bytes := by
  simp [bytes?]

private theorem longest_single (c : UInt8) (bytes : List UInt8) (limit : Nat) :
    longest [[c]] bytes limit =
      if 1 ≤ limit ∧ bytes.head? = some c then some 1 else none := by
  cases bytes with
  | nil => simp [longest]
  | cons b rest =>
    by_cases same : b = c
    · subst same; simp [longest]
    · simp [longest, same, Ne.symm same]

private theorem find_none (c : UInt8) (low high : Nat) :
    ∀ (bytes : List UInt8) (offset : Nat), c ∉ bytes →
      find [[c]] low high bytes offset = none
  | [], _, _ => by simp [find]
  | b :: rest, offset, absent => by
    simp only [List.mem_cons, not_or] at absent
    have ih := find_none c low high rest (offset + 1) absent.2
    have head : longest [[c]] (b :: rest) (high - offset) = none := by
      simp [longest_single, Ne.symm absent.1]
    rw [find, head, ih]
    split <;> (try split) <;> rfl

private theorem find_first (c : UInt8) (low high : Nat) (tail : List UInt8) :
    ∀ (before : List UInt8) (offset : Nat), c ∉ before → low ≤ offset →
      offset + before.length < high →
      find [[c]] low high (before ++ c :: tail) offset = some (offset + before.length, 1)
  | [], offset, _, lower, below => by
    simp only [List.length_nil, Nat.add_zero] at below
    have head : longest [[c]] (c :: tail) (high - offset) = some 1 := by
      simp [longest_single]; omega
    rw [List.nil_append, find, ite_eq_right (by omega), ite_eq_right (by omega), head]
    rfl
  | b :: rest, offset, absent, lower, below => by
    simp only [List.mem_cons, not_or] at absent
    simp only [List.length_cons] at below
    have ih := find_first c low high tail rest (offset + 1) absent.2 (by omega) (by omega)
    have head : longest [[c]] (b :: (rest ++ c :: tail)) (high - offset) = none := by
      simp [longest_single, Ne.symm absent.1]
    rw [List.cons_append, find, ite_eq_right (by omega), ite_eq_right (by omega), head, ih]
    simp only [List.length_cons]
    congr 2
    omega

private theorem length_le_intercalate (c : UInt8) :
    ∀ (separated : List (List UInt8)),
      separated.length ≤ (List.intercalate [c] separated).length + 1
  | [] => by simp
  | [_] => by simp
  | part :: next :: rest => by
    have := length_le_intercalate c (next :: rest)
    rw [List.intercalate_cons_cons]
    simp only [List.length_append, List.length_cons] at *
    omega

private theorem parts_global (c : UInt8) (high : Nat) :
    ∀ (separated : List (List UInt8)) (fuel offset : Nat), separated ≠ [] →
      (∀ part ∈ separated, c ∉ part) → separated.length ≤ fuel + 1 →
      offset + (List.intercalate [c] separated).length = high →
      parts [[c]] 0 high true fuel (List.intercalate [c] separated) offset = separated
  | [], _, _, nonempty, _, _, _ => absurd rfl nonempty
  | [part], fuel, offset, _, absent, _, _ => by
    have none := find_none c 0 high part offset (absent part (by simp))
    cases fuel <;> simp [parts, none]
  | part :: next :: rest, fuel, offset, _, absent, enough, size => by
    have partAbsent := absent part (by simp)
    have restAbsent : ∀ p ∈ next :: rest, c ∉ p := fun p mem => absent p (by simp [mem])
    rw [List.intercalate_cons_cons] at size ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at size
    obtain ⟨fuel, rfl⟩ : ∃ previous, fuel = previous + 1 :=
      ⟨fuel - 1, by simp only [List.length_cons] at enough; omega⟩
    have first := find_first c 0 high (List.intercalate [c] (next :: rest)) part offset
      partAbsent (Nat.zero_le _) (by omega)
    have ih := parts_global c high (next :: rest) fuel (offset + part.length + 1)
      (by simp) restAbsent (by simp only [List.length_cons] at enough ⊢; omega) (by omega)
    rw [List.append_assoc, List.singleton_append, parts, first]
    simp only [Nat.add_sub_cancel_left, ite_true]
    have take : List.take part.length (part ++ c :: List.intercalate [c] (next :: rest)) = part := by
      simp
    have drop : List.drop (part.length + 1) (part ++ c :: List.intercalate [c] (next :: rest)) =
        List.intercalate [c] (next :: rest) := by
      simp [List.drop_append]
    rw [take, drop, ih]

/-- Splitting at every separator recovers the parts that the separator joins. -/
theorem split_global_intercalate (c : UInt8) (separated : List (List UInt8))
    (nonempty : separated ≠ []) (absent : ∀ part ∈ separated, c ∉ part) :
    «split/3» (.bitstring ⟨(List.intercalate [c] separated).toArray⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) (Term.list [.atom "global"]) =
      .ok (Term.list (separated.map fun part =>
        .bitstring ⟨part.toArray⟩ 0 (Term.Bitstring.valid_aligned _))) := by
  have whole := parts_global c (List.intercalate [c] separated).length separated
    (List.intercalate [c] separated).length 0 nonempty absent ?_ (by simp)
  · have pattern : bytes? (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) = some [c] :=
      bytes?_binary [c]
    simp [«split/3», bytes?_binary, patterns?, pattern, properList?, splitOptions?, whole,
      binary_eq]
  · exact length_le_intercalate c separated

/-- Splitting once at a separator absent from the first part. -/
theorem split_first (c : UInt8) (before after : List UInt8) (absent : c ∉ before) :
    «split/2» (.bitstring ⟨(before ++ c :: after).toArray⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) =
      .ok (Term.list [.bitstring ⟨before.toArray⟩ 0 (Term.Bitstring.valid_aligned _),
        .bitstring ⟨after.toArray⟩ 0 (Term.Bitstring.valid_aligned _)]) := by
  have first := find_first c 0 (before ++ c :: after).length after before 0 absent
    (Nat.zero_le _) (by simp)
  have pattern : bytes? (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) = some [c] :=
    bytes?_binary [c]
  obtain ⟨fuel, size⟩ : ∃ fuel, (before ++ c :: after).length = fuel + 1 := ⟨_, by simp; rfl⟩
  simp only [«split/2», «split/3», bytes?_binary, pattern, patterns?, properList?,
    splitOptions?, Option.bind_some]
  generalize (before ++ c :: after).length = n at first size ⊢
  subst size
  simp [parts, first, binary_eq]

/-- A binary without the separator splits into itself. -/
theorem split_absent (c : UInt8) (bytes : List UInt8) (absent : c ∉ bytes) :
    «split/2» (.bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) =
      .ok (Term.list [.bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _)]) := by
  have pattern : bytes? (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) = some [c] :=
    bytes?_binary [c]
  have none := find_none c 0 bytes.length bytes 0 absent
  simp only [«split/2», «split/3», bytes?_binary, pattern, patterns?, properList?,
    splitOptions?, Option.bind_some]
  generalize bytes.length = n at none ⊢
  cases n <;> simp [parts, none, binary_eq]

/-- The first occurrence of a byte is its leftmost match. -/
theorem match_first (c : UInt8) (before after : List UInt8) (absent : c ∉ before) :
    «match/2» (.bitstring ⟨(before ++ c :: after).toArray⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) =
      .ok (.tuple #[.integer before.length, .integer 1]) := by
  have first := find_first c 0 (before ++ c :: after).length after before 0 absent
    (Nat.zero_le _) (by simp)
  have pattern : bytes? (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) = some [c] :=
    bytes?_binary [c]
  simp only [«match/2», «match/3», bytes?_binary, pattern, patterns?, properList?, List.foldl_nil]
  generalize (before ++ c :: after).length = n at first ⊢
  simp [first]

/-- A binary without the byte does not match it. -/
theorem match_absent (c : UInt8) (bytes : List UInt8) (absent : c ∉ bytes) :
    «match/2» (.bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) = .ok (.atom "nomatch") := by
  have pattern : bytes? (.bitstring ⟨#[c]⟩ 0 (Term.Bitstring.valid_aligned _)) = some [c] :=
    bytes?_binary [c]
  simp [«match/2», «match/3», bytes?_binary, pattern, patterns?, properList?,
    find_none c 0 bytes.length bytes 0 absent]

theorem last_binary (bytes : List UInt8) (nonempty : bytes ≠ []) :
    «last/1» (.bitstring ⟨bytes.toArray⟩ 0 (Term.Bitstring.valid_aligned _)) =
      .ok (.integer (bytes.getLast nonempty).toNat) := by
  simp [«last/1», bytes?_binary, List.getLast?_eq_some_getLast nonempty]

end Erlang.binary
