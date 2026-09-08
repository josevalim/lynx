import Lynx

namespace LynxTest.Modules.Maps
open Lynx Lynx.Modules
open Lynx.Term.Map

/-- Arbitrary terms need no validity assumptions. -/
theorem get_after_put (m k v : Term) (hm : Extensions.is_map_2 m (fun _ _ => .ok Term.true) = .ok Term.true) :
    (Maps.put_3 k v m >>= Maps.get_2 k) = .ok v := by lynx_verify

theorem merge_associative (a b c : Term)
    (ha : Extensions.is_map_2 a (fun _ _ => .ok Term.true) = .ok Term.true) (hb : Extensions.is_map_2 b (fun _ _ => .ok Term.true) = .ok Term.true)
    (hc : Extensions.is_map_2 c (fun _ _ => .ok Term.true) = .ok Term.true) :
    (Maps.merge_2 a b >>= fun ab => Maps.merge_2 ab c) =
    (Maps.merge_2 b c >>= Maps.merge_2 a) := by lynx_verify

private def a : Term := .atom "a"
private def b : Term := .atom "b"
private def one : Term := .integer 1
private def two : Term := .integer 2

theorem new_and_get :
    Maps.new_0 = .ok Term.empty_map ∧
    Maps.get_2 a (.map [(a, one)]) = .ok one := by
  repeat' first | apply And.intro | rfl

theorem missing_key (key : Term) :
    Maps.get_2 key Term.empty_map = .error (.error (.tuple #[.atom "badkey", key])) := rfl

theorem put_overwrites :
    (Maps.put_3 a one Term.empty_map >>= Maps.put_3 a two) = .ok (.map [(a, two), (a, one)]) := by
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
    Maps.merge_2 bad Term.empty_map = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Maps.merge_2 Term.empty_map bad = .error (.error (.tuple #[.atom "badmap", bad])) := by
  intro bad h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [Maps.get_2, Maps.put_3, Maps.merge_2, one, Term.empty_map]

end LynxTest.Modules.Maps
