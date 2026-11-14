namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- The kinds of keys of the bits of bitmaps. -/
def bitKind : Nat → String
  | 0 => "binary"
  | 1 => "bitstring_no_binary"
  | 2 => "list"
  | 3 => "integer"
  | 4 => "float"
  | 5 => "pid"
  | 6 => "port"
  | _ => "reference"

theorem testBit_and_pow (x i : Nat) : (x &&& 2 ^ i ≠ 0) ↔ x.testBit i = Bool.true := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Nat.testBit_two_pow] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    rw [hj.2]; exact hj.1
  · intro h e
    have := Nat.testBit_and x (2 ^ i) i
    rw [e, Nat.zero_testBit, Nat.testBit_two_pow_self, h] at this
    cases this

theorem ne_bit (x i : Nat) : Erlang.erlang.«/=/2» (.integer (Int.ofNat (x &&& 2 ^ i))) (.integer 0) =
    .ok (boolAtom (x.testBit i)) := by
  have := testBit_and_pow x i
  cases h : x.testBit i <;> simp_all [Erlang.erlang.«/=/2», boolAtom, Term.false, Term.true]

theorem band_nat (x m : Nat) :
    Erlang.erlang.«band/2» (.integer (Int.ofNat x)) (.integer (Int.ofNat m)) = .ok (.integer (Int.ofNat (x &&& m))) :=
  rfl

theorem bit_case (c : Bool) (a y : Term) :
    Elixir.Module.Types.Descr.«atom_intersection/2».match_3 (fun _ => Except Exception Term) (boolAtom c)
      (fun _ => pure y) (fun _ => pure (a.cons y))
      (fun u => Except.error (Exception.error (.tuple #[.atom "case_clause", u]))) =
      .ok (if c then a.cons y else y) := by
  cases c <;> rfl

/-- A list with an element added when a condition holds. -/
def ccons (c : Bool) (a : Term) (l : List Term) : List Term := if c then a :: l else l

theorem ccons_list (c : Bool) (a : Term) (l : List Term) :
    (if c = Bool.true then a.cons (Term.list l) else Term.list l) = Term.list (ccons c a l) := by
  cases c <;> rfl

theorem ccons_append (c : Bool) (a : Term) (l acc : List Term) : ccons c a l ++ acc = ccons c a (l ++ acc) := by
  cases c <;> rfl

theorem mem_ccons {c : Bool} {a d : Term} {l : List Term} : d ∈ ccons c a l ↔ (c = Bool.true ∧ d = a) ∨ d ∈ l := by
  cases c <;> simp [ccons]

theorem exists_lt_eight {P : Nat → Prop} :
    (∃ i < 8, P i) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 ∨ P 7 := by
  constructor
  · rintro ⟨i, hi, h⟩
    match i, hi with
    | 0, _ => exact Or.inl h
    | 1, _ => exact Or.inr (Or.inl h)
    | 2, _ => exact Or.inr (Or.inr (Or.inl h))
    | 3, _ => exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    | 4, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    | 5, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    | 6, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    | 7, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
    · exact ⟨3, by omega, h⟩
    · exact ⟨4, by omega, h⟩
    · exact ⟨5, by omega, h⟩
    · exact ⟨6, by omega, h⟩
    · exact ⟨7, by omega, h⟩

/-- `bitmap_to_domain_keys/2` adds the kinds of the bits of a bitmap. -/
theorem bitmap_keys (x : Nat) (acc : List Term) :
    ∃ pre, Elixir.Module.Types.Descr.«bitmap_to_domain_keys/2» (.integer (x : Int)) (Term.list acc) =
      .ok (Term.list (pre ++ acc)) ∧ ∀ d, d ∈ pre ↔ ∃ i < 8, x.testBit i = Bool.true ∧ d = .atom (bitKind i) := by
  have a0 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 1) = .ok (.integer (Int.ofNat (x &&& 2 ^ 0))) :=
    band_nat x 1
  have a1 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 2) = .ok (.integer (Int.ofNat (x &&& 2 ^ 1))) :=
    band_nat x 2
  have a2 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 4) = .ok (.integer (Int.ofNat (x &&& 2 ^ 2))) :=
    band_nat x 4
  have a3 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 8) = .ok (.integer (Int.ofNat (x &&& 2 ^ 3))) :=
    band_nat x 8
  have a4 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 16) = .ok (.integer (Int.ofNat (x &&& 2 ^ 4))) :=
    band_nat x 16
  have a5 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 32) = .ok (.integer (Int.ofNat (x &&& 2 ^ 5))) :=
    band_nat x 32
  have a6 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 64) = .ok (.integer (Int.ofNat (x &&& 2 ^ 6))) :=
    band_nat x 64
  have a7 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 128) = .ok (.integer (Int.ofNat (x &&& 2 ^ 7))) :=
    band_nat x 128
  refine ⟨(ccons (x.testBit 7) (.atom "reference") (ccons (x.testBit 6) (.atom "port") (ccons (x.testBit 5) (.atom "pid")
    (ccons (x.testBit 4) (.atom "float") (ccons (x.testBit 3) (.atom "integer") (ccons (x.testBit 2) (.atom "list")
    (ccons (x.testBit 1) (.atom "bitstring_no_binary") (ccons (x.testBit 0) (.atom "binary") [])))))))), ?_, fun d => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«bitmap_to_domain_keys/2», a0, a1, a2, a3, a4, a5, a6, a7, Lynx.Except.ok_bind,
      ne_bit, bit_case, ccons_list, ccons_append, List.nil_append]
  · simp only [mem_ccons, List.not_mem_nil, or_false, exists_lt_eight, bitKind]
    simp only [or_comm, or_left_comm, or_assoc]

end Elixir.STTDescrProofsTest.Nest
