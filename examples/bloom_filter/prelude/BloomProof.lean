module
public import Lynx
public import Lynx.Modules.Erlang.erlang
public section

namespace BloomProof
open Lynx

/-- A proper list of bit positions. -/
@[expose] def indices (ps : List Nat) : Term := Term.list (ps.map fun p : Nat => .integer (p : Int))

@[simp] theorem indices_nil : indices [] = .nil := rfl
@[simp] theorem indices_cons (p : Nat) (ps : List Nat) :
    indices (p :: ps) = .cons (.integer p) (indices ps) := rfl

/-- The bits after setting each position, as `add/2` computes them. -/
@[expose] def add (bits : Nat) (ps : List Nat) : Nat := ps.foldl (fun b p => b ||| 2 ^ p) bits

theorem testBit_add (bits : Nat) (ps : List Nat) (i : Nat) :
    (add bits ps).testBit i = (bits.testBit i || ps.contains i) := by
  induction ps generalizing bits with
  | nil => simp [add]
  | cons p ps ih =>
    simp only [add, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases h : i = p
    · subst h; simp
    · have other : ¬p = i := fun e => h e.symm
      simp [h, other]

theorem add_or (bits : Nat) (ps : List Nat) : add bits ps = bits ||| add 0 ps := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [testBit_add]

/-- The number of set bits below `p`. -/
@[expose] def ones (bits : Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => (if bits.testBit p then 1 else 0) + ones bits p

/-! The bit operations on natural numbers, stated in simp normal form. -/

theorem bsl_one (p : Nat) :
    Erlang.erlang.«bsl/2» (.integer 1) (.integer p) = .ok (.integer (2 ^ p)) := by
  simp [Erlang.erlang.«bsl/2», Int.shiftLeft_eq]

theorem bor_two_pow (bits p : Nat) :
    Erlang.erlang.«bor/2» (.integer bits) (.integer (2 ^ p)) =
      .ok (.integer (bits ||| 2 ^ p : Nat)) := by
  have power : (2 : Int) ^ p = ((2 ^ p : Nat) : Int) := by simp
  rw [power]
  rfl

theorem bor_nat (left right : Nat) :
    Erlang.erlang.«bor/2» (.integer left) (.integer right) =
      .ok (.integer (left ||| right : Nat)) := rfl

theorem bsr_nat (bits p : Nat) :
    Erlang.erlang.«bsr/2» (.integer bits) (.integer p) = .ok (.integer ((bits : Int) >>> p)) := rfl

theorem bit (bits p : Nat) :
    Erlang.erlang.«band/2» (.integer ((bits : Int) >>> p)) (.integer 1) =
      .ok (.integer (if bits.testBit p then 1 else 0)) := by
  have h := Nat.testBit_eq_decide_div_mod_eq (x := bits) (i := p)
  have masked : (bits >>> p) &&& 1 = if bits.testBit p then 1 else 0 := by
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    split <;> simp_all <;> omega
  have shifted : (bits : Int) >>> p = ((bits >>> p : Nat) : Int) := rfl
  rw [shifted]
  show (Except.ok (Term.integer ((bits >>> p) &&& 1 : Nat)) : Except Exception Term) = _
  rw [masked]
  split <;> rfl

end BloomProof
