import LynxTest.ProofAudit
import Lynx

namespace LynxTest.Modules.Maps
open Lynx Lynx.Modules
open Lynx.Term.Map

/-- Arbitrary terms need no validity assumptions. -/
theorem get_after_put (m k v : Term)
    (hm : m.isMap = true) :
    (Maps.put_3 k v m >>= Maps.get_2 k) = .ok v := by
  obtain ⟨entries, rfl⟩ := Term.isMap_iff m |>.mp hm
  simp [Maps.put_3, Maps.get_2]

theorem merge_associative (a b c : Term)
    (ha : a.isMap = true) (hb : b.isMap = true) (hc : c.isMap = true) :
    (Maps.merge_2 a b >>= fun ab => Maps.merge_2 ab c) =
    (Maps.merge_2 b c >>= Maps.merge_2 a) := by
  obtain ⟨left, rfl⟩ := Term.isMap_iff a |>.mp ha
  obtain ⟨middle, rfl⟩ := Term.isMap_iff b |>.mp hb
  obtain ⟨right, rfl⟩ := Term.isMap_iff c |>.mp hc
  simp [Maps.merge_2]

private def a : Term := .atom "a"
private def b : Term := .atom "b"
private def one : Term := .integer 1
private def two : Term := .integer 2
private def floatOne : Term.FiniteFloat :=
  ⟨false, 1023, 0⟩

theorem new_and_get :
    Maps.new_0 = .ok Term.emptyMap ∧
    Maps.get_2 a (.map [(a, one)]) = .ok one := by
  repeat' first | apply And.intro | rfl

theorem missing_key (key : Term) :
    Maps.get_2 key Term.emptyMap = .error (.error (.tuple #[.atom "badkey", key])) := rfl

theorem numeric_key_types_are_distinct :
    Maps.get_2 (.integer 1) (.map [(.float floatOne, a)]) =
      .error (.error (.tuple #[.atom "badkey", .integer 1])) ∧
    Maps.get_2 (.float floatOne) (.map [(.integer 1, a)]) =
      .error (.error (.tuple #[.atom "badkey", .float floatOne])) := by
  exact ⟨rfl, rfl⟩

theorem put_overwrites :
    (Maps.put_3 a one Term.emptyMap >>= Maps.put_3 a two) = .ok (.map [(a, two), (a, one)]) := by
  repeat' first | apply And.intro | rfl

theorem merge_bindings :
    Maps.merge_2 (.map [(a, one)]) (.map [(b, two)]) = .ok (.map [(b, two), (a, one)]) ∧
    Maps.merge_2 (.map [(a, one)]) (.map [(a, two)]) = .ok (.map [(a, two), (a, one)]) ∧
    Maps.merge_2 (.map [(a, two)]) (.map [(a, one)]) = .ok (.map [(a, one), (a, two)]) := by
  repeat' first | apply And.intro | rfl

/-- Only nonmaps raise badmap, preserving the offending argument. -/
theorem bad_maps : ∀ bad ∈ [one, .nil, .tuple #[]],
    Maps.get_2 a bad = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Maps.put_3 a one bad = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Maps.merge_2 bad Term.emptyMap = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Maps.merge_2 Term.emptyMap bad = .error (.error (.tuple #[.atom "badmap", bad])) := by
  intro bad h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [Maps.get_2, Maps.put_3, Maps.merge_2, one, Term.emptyMap]

end LynxTest.Modules.Maps

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Maps
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Maps
