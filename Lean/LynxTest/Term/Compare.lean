module

public meta import LynxTest.ProofAudit
public import Lynx.Term
import all Lynx.Term.Compare
import all Lynx.Term.FiniteFloat
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Term.Compare
open Lynx

private def floatOne : Term.FiniteFloat :=
  ⟨false, 1023, 0⟩

private def positiveZero : Term.FiniteFloat :=
  ⟨false, 0, 0⟩

private def negativeZero : Term.FiniteFloat :=
  ⟨true, 0, 0⟩

private theorem floatOne_toRat : floatOne.toRat = 1 := by
  simp [floatOne, Term.FiniteFloat.toRat, Term.FiniteFloat.magnitude]
  change (4503599627370496 : Rat) * 2 ^ (-52 : Int) = 1
  rw [show (-52 : Int) = -(52 : Int) by rfl, Rat.zpow_neg]
  change (2 : Rat) ^ (52 : Nat) * ((2 : Rat) ^ (52 : Nat))⁻¹ = 1
  exact Rat.mul_inv_cancel _ (by decide)

-- Strictly increasing across every represented category. Tuples compare arity
-- before elements; maps compare size, all keys, then values. Includes nested
-- tuples/maps, Unicode atoms, large integers, improper tails, and list prefixes.
@[expose] public def orderedTerms : List Term := [
  .integer (-1000000000000000000000000000000), .integer (-1), .integer 0,
  .integer 1000000000000000000000000000000,
  .atom "", .atom "a", .atom "aa", .atom "b", .atom "é", .atom "λ", .atom "😀",
  .reference [], .reference [0], .reference [1], .reference [1, 0],
  .reference [1000000000000000000000000000000],
  .function "a" "f" 1 #[], .function "a" "f" 1 #[.integer 10],
  .function "a" "f" 1 #[.integer 20], .function "a" "f" 2 #[], .function "a" "g" 0 #[],
  .function "b" "a" 0 #[],
  .pid [], .pid [0], .pid [1], .pid [1, 0], .pid [1000000000000000000000000000000],
  .tuple #[],
  .tuple #[.integer (-1)], .tuple #[.integer 0], .tuple #[.atom "a"],
  .tuple #[.tuple #[]], .tuple #[(Term.map [])], .tuple #[.nil],
  .tuple #[.integer (-100), .integer 0],
  .tuple #[.integer 0, .integer 0], .tuple #[.integer 0, .integer 1],
  .tuple #[.integer 1, .integer 0],
  (Term.map []),
  Term.map [(.integer 0, .integer 0)],
  Term.map [(.integer 0, .integer 1)],
  Term.map [(.integer 1, .integer (-99))],
  Term.map [(.atom "a", .nil)],
  Term.map [(.tuple #[], .nil)],
  Term.map [((Term.map []), .nil)],
  Term.map [(.atom "a", .integer 99), (.atom "b", .integer 0)],
  Term.map [(.atom "a", .integer 0), (.atom "c", .integer 0)],
  Term.map [(.atom "a", .integer 0), (.atom "c", .integer 1)],
  Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 2, .nil)],
  .nil,
  .cons (.integer (-1)) .nil,
  .cons (.integer 0) (.integer (-1)),
  .cons (.integer 0) (.atom "a"),
  .cons (.integer 0) .nil,
  .cons (.integer 0) (.cons (.integer 0) .nil),
  .cons (.integer 0) (.cons (.integer 1) .nil),
  .cons (.integer 0) (.cons (.cons (.integer 0) .nil) .nil),
  .cons (.integer 1) .nil,
  .cons (.atom "a") .nil,
  .cons .nil .nil,
  .cons (.cons (.integer 0) .nil) .nil]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem ordered_terms :
    orderedTerms.Pairwise (fun a b =>
      Term.compare (Term.fuel a b) a b = .lt ∧ Term.compare (Term.fuel b a) b a = .gt) := by decide

theorem closure_captures_comparison :
    Term.compare (Term.fuel (.function "a" "f" 1 #[.integer 10]) (.function "a" "f" 1 #[.integer 20])) (.function "a" "f" 1 #[.integer 10]) (.function "a" "f" 1 #[.integer 20]) = .lt ∧
    Term.compare (Term.fuel (.function "a" "f" 1 #[.integer 20]) (.function "a" "f" 1 #[.integer 10])) (.function "a" "f" 1 #[.integer 20]) (.function "a" "f" 1 #[.integer 10]) = .gt ∧
    Term.compareExact (Term.fuel (.function "a" "f" 1 #[.integer 10]) (.function "a" "f" 1 #[.integer 20])) (.function "a" "f" 1 #[.integer 10]) (.function "a" "f" 1 #[.integer 20]) ≠ .eq ∧
    Term.compareExact (Term.fuel (.function "a" "f" 1 #[.integer 10]) (.function "a" "f" 1 #[.integer 10])) (.function "a" "f" 1 #[.integer 10]) (.function "a" "f" 1 #[.integer 10]) = .eq ∧
    Term.compare (Term.fuel (.function "a" "f" 1 #[.integer 20]) (.function "a" "g" 1 #[.integer 10])) (.function "a" "f" 1 #[.integer 20]) (.function "a" "g" 1 #[.integer 10]) = .lt := by
  decide

theorem numeric_and_exact_comparison :
    Term.compare (Term.fuel (.integer 1) (.float floatOne)) (.integer 1) (.float floatOne) = .eq ∧
    Term.compareExact (Term.fuel (.integer 1) (.float floatOne)) (.integer 1) (.float floatOne) = .lt ∧
    Term.compare (Term.fuel (.tuple #[.integer 1]) (.tuple #[.float floatOne])) (.tuple #[.integer 1]) (.tuple #[.float floatOne]) = .eq ∧
    Term.compareExact (Term.fuel (.tuple #[.integer 1]) (.tuple #[.float floatOne])) (.tuple #[.integer 1]) (.tuple #[.float floatOne]) = .lt ∧
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(.atom "key", .integer 1)])
      (.map [(.atom "key", .float floatOne)]) = .eq ∧
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(.integer 1, .nil)])
      (.map [(.float floatOne, .nil)]) = .lt := by
  simp [Term.compare_tuple, Term.compareExact_tuple, Term.compare_singleton_map,
    List.compareLex_cons_cons, List.compareLex_nil_nil, floatOne_toRat]

theorem signed_zero_comparison :
    Term.compare (Term.fuel (.float positiveZero) (.float negativeZero)) (.float positiveZero) (.float negativeZero) = .eq ∧
    Term.compareExact (Term.fuel (.float positiveZero) (.float negativeZero)) (.float positiveZero) (.float negativeZero) ≠ .eq := by
  simp [positiveZero, negativeZero]

/-- Size counts effective keys; key comparison precedes every value comparison. -/
theorem association_list_order :
    let a := Term.atom "a"
    let b := Term.atom "b"
    let c := Term.atom "c"
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(a, .nil), (a, .integer 99)])
      (.map [(b, .nil), (a, .nil)]) = .lt ∧
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(b, .integer 0), (a, .integer 99)])
      (.map [(c, .integer 0), (a, .integer 0)]) = .lt ∧
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(b, .integer 0), (a, .integer 99)])
      (.map [(a, .integer 99), (b, .integer 1)]) = .lt ∧
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(b, .nil), (a, .integer 1), (a, .integer 99)])
      (.map [(a, .integer 1), (b, .nil)]) = .eq := by decide

/-- Comparison reaches map keys and values through every recursive constructor. -/
theorem nested_map_order :
    let x := Term.map [(.integer 1, .nil), (.integer 0, .nil)]
    let y := Term.map [(.integer 0, .nil), (.integer 1, .nil), (.integer 1, .integer 99)]
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(x, .tuple #[.cons y x])])
      (.map [(y, .tuple #[.cons x y])]) = .eq ∧
    (fun a b => Term.compare (Term.fuel a b) a b) (.map [(x, .integer 0), (y, .integer 99)])
      (.map [(y, .integer 1)]) = .lt := by decide

/-- Constructor rank and tuple arity decide without comparing children. -/
theorem comparison_short_circuit (a b : Term) :
    Term.compare (Term.fuel (.integer 0) (.map [(a,b)])) (.integer 0) (.map [(a,b)]) = .lt ∧
    Term.compare (Term.fuel (.tuple #[a,b]) (.tuple #[b])) (.tuple #[a,b]) (.tuple #[b]) = .gt ∧
    Term.compare (Term.fuel (.map [(a,b)]) (.map [])) (.map [(a,b)]) (.map []) = .gt := by
  refine ⟨Term.compare_integer_map 0 [(a,b)], ?_, Term.compare_singleton_map_empty a b⟩
  rw [Term.compare_tuple]
  rfl

/-- A decisive head/key comparison makes the tails/values irrelevant. -/
theorem comparison_keys_before_values (k l v w : Term)
    (head : Term.compare (Term.fuel k l) k l = .lt) (key : Term.compareExact (Term.fuel k l) k l = .lt) :
    Term.compare (Term.fuel (.cons k v) (.cons l w)) (.cons k v) (.cons l w) = .lt ∧
    Term.compare (Term.fuel (.map [(k,v)]) (.map [(l,w)])) (.map [(k,v)]) (.map [(l,w)]) = .lt := by
  simp [Term.compare_cons, Term.compare_singleton_map, head, key]

/-- Lists exactly compare their heads first. -/
theorem exact_comparison_heads_first (a as b bs : Term) (head : Term.compareExact (Term.fuel a b) a b = .lt) :
    Term.compareExact (Term.fuel (.cons a as) (.cons b bs)) (.cons a as) (.cons b bs) = .lt := by
  simp [Term.compareExact_cons, head]

/-- Shadowed bindings do not affect exact map equality. -/
theorem exact_map_equality_by_lookup (k v w : Term) :
    Term.compareExact (Term.fuel (.map [(k, v), (k, w)]) (.map [(k, v)])) (.map [(k, v), (k, w)]) (.map [(k, v)]) = .eq := by
  apply Term.map_compareExact_eq_of_lookup
  intro q
  by_cases same : Term.compareExact (Term.fuel q k) q k = .eq <;> simp [same]

/-- Exactly equal maps bind the same keys. -/
theorem exact_map_equality_lookup (k v : Term) :
    Term.compareExact (Term.fuel (.map [(k, v)]) (.map [])) (.map [(k, v)]) (.map []) ≠ .eq := by
  intro equal
  have rel := Term.lookup_of_map_compareExact_eq _ _ equal k
  simp at rel

/-- Semantically equal maps bind the same keys. -/
theorem map_equality_lookup (k v : Term) :
    Term.compare (Term.fuel (.map [(k, v)]) (.map [])) (.map [(k, v)]) (.map []) ≠ .eq := by
  intro equal
  have rel := Term.lookup_of_map_compare_eq _ _ equal k
  simp at rel

/-- Binaries are never exactly equal to other kinds of terms, such as `[]` or `%{}`. -/
theorem binary_exact_kinds (bytes : ByteArray) :
    Term.compareExact (Term.fuel (.bitstring bytes 0 (Term.Bitstring.valid_aligned _)) .nil) (.bitstring bytes 0 (Term.Bitstring.valid_aligned _)) .nil ≠ .eq ∧
    Term.compareExact (Term.fuel (.bitstring bytes 0 (Term.Bitstring.valid_aligned _)) (.map [])) (.bitstring bytes 0 (Term.Bitstring.valid_aligned _)) (.map []) ≠ .eq := by
  constructor <;> intro equal <;>
    obtain ⟨_, _, _, kind⟩ := Term.bitstring_compareExact_eq _ _ _ _ equal <;> cases kind

/-- Nonempty lists are never exactly equal to `[]` or `%{}`. -/
theorem list_exact_kinds (head tail : Term) :
    Term.compareExact (Term.fuel (.cons head tail) .nil) (.cons head tail) .nil ≠ .eq ∧ Term.compareExact (Term.fuel (.cons head tail) (.map [])) (.cons head tail) (.map []) ≠ .eq := by
  constructor <;> intro equal <;>
    obtain ⟨_, _, kind⟩ := Term.cons_compareExact_eq _ _ _ equal <;> cases kind

/-- Binaries are exactly equal when their bytes are. -/
theorem binary_exact_bytes :
    (fun a b => Term.compareExact (Term.fuel a b) a b) (.bitstring ⟨#[1, 2]⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[1, 2]⟩ 0 (Term.Bitstring.valid_aligned _)) = .eq ∧
      (fun a b => Term.compareExact (Term.fuel a b) a b) (.bitstring ⟨#[1, 2]⟩ 0 (Term.Bitstring.valid_aligned _))
        (.bitstring ⟨#[1]⟩ 0 (Term.Bitstring.valid_aligned _)) ≠ .eq := by
  refine ⟨(Term.binary_compareExact_eq _ _).mpr rfl, fun equal => ?_⟩
  have := (Term.binary_compareExact_eq _ _).mp equal
  simp [ByteArray.mk.injEq] at this

end LynxTest.Term.Compare

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.Compare
  LynxTest.ProofAudit.checkModule `LynxTest.Term.Compare
