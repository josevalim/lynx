module

import Lynx.Modules.Erlang.maps
import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit
import Lynx
import all Lynx.Term.Compare
import all Std
import all Init.Data.List.Basic
import all Init.Data.List.Control
import all Init.Data.Ord.String

namespace LynxTest.Modules.Maps
open Lynx

theorem get_after_put (m k v : Term)
    (hm : ∃ entries, m = .map entries) :
    (Erlang.maps.«put/3» k v m >>= Erlang.maps.«get/2» k) = .ok v := by
  exact Erlang.maps.get_after_put m k v hm

theorem merge_associative (a b c : Term)
    (ha : ∃ entries, a = .map entries) (hb : ∃ entries, b = .map entries) (hc : ∃ entries, c = .map entries) :
    (Erlang.maps.«merge/2» a b >>= fun ab => Erlang.maps.«merge/2» ab c) =
    (Erlang.maps.«merge/2» b c >>= Erlang.maps.«merge/2» a) := by
  exact Erlang.maps.merge_associative a b c ha hb hc

private def a : Term := .atom "a"
private def b : Term := .atom "b"
private def one : Term := .integer 1
private def two : Term := .integer 2
private def floatOne : Term.FiniteFloat :=
  ⟨false, 1023, 0⟩

theorem new_and_get :
    Erlang.maps.«new/0» = .ok (Term.map []) ∧
    Erlang.maps.«get/2» a (.map [(a, one)]) = .ok one := by
  repeat' first | apply And.intro | rfl

theorem missing_key (key : Term) :
    Erlang.maps.«get/2» key (Term.map []) = .error (.error (.tuple #[.atom "badkey", key])) := rfl

theorem numeric_key_types_are_distinct :
    Erlang.maps.«get/2» (.integer 1) (.map [(.float floatOne, a)]) =
      .error (.error (.tuple #[.atom "badkey", .integer 1])) ∧
    Erlang.maps.«get/2» (.float floatOne) (.map [(.integer 1, a)]) =
      .error (.error (.tuple #[.atom "badkey", .float floatOne])) := by
  exact ⟨rfl, rfl⟩

theorem put_overwrites :
    (Erlang.maps.«put/3» a one (Term.map []) >>= Erlang.maps.«put/3» a two) = .ok (.map [(a, two), (a, one)]) := by
  repeat' first | apply And.intro | rfl

theorem merge_bindings :
    Erlang.maps.«merge/2» (.map [(a, one)]) (.map [(b, two)]) = .ok (.map [(b, two), (a, one)]) ∧
    Erlang.maps.«merge/2» (.map [(a, one)]) (.map [(a, two)]) = .ok (.map [(a, two), (a, one)]) ∧
    Erlang.maps.«merge/2» (.map [(a, two)]) (.map [(a, one)]) = .ok (.map [(a, one), (a, two)]) := by
  repeat' first | apply And.intro | rfl

/-- Only nonmaps raise badmap, preserving the offending argument. -/
theorem bad_maps : ∀ bad ∈ [one, .nil, .tuple #[]],
    Erlang.maps.«get/2» a bad = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Erlang.maps.«put/3» a one bad = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Erlang.maps.«merge/2» bad (Term.map []) = .error (.error (.tuple #[.atom "badmap", bad])) ∧
    Erlang.maps.«merge/2» (Term.map []) bad = .error (.error (.tuple #[.atom "badmap", bad])) := by
  intro bad h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [Erlang.maps.«get/2», Erlang.maps.«put/3», Erlang.maps.«merge/2», one]

theorem update_existing :
    Erlang.maps.«update/3» a two (.map [(a, one)]) = .ok (.map [(a, two), (a, one)]) := rfl

theorem update_missing (key value : Term) :
    Erlang.maps.«update/3» key value (.map []) =
      .error (.error (.tuple #[.atom "badkey", key])) := rfl

theorem update_numeric_keys :
    Erlang.maps.«update/3» (.integer 1) two (.map [(.float floatOne, one)]) =
      .error (.error (.tuple #[.atom "badkey", .integer 1])) := rfl

theorem mixed_same_key :
    (Erlang.maps.«put/3» a one (.map []) >>= Erlang.maps.«update/3» a two) =
      .ok (.map [(a, two), (a, one)]) ∧
    (Erlang.maps.«update/3» a one (.map []) >>= Erlang.maps.«put/3» a two) =
      .error (.error (.tuple #[.atom "badkey", a])) := ⟨rfl, rfl⟩

theorem update_badmap (n : Int) :
    Erlang.maps.«update/3» a one (.integer n) =
      .error (.error (.tuple #[.atom "badmap", .integer n])) := rfl

theorem update_lookup (m key value old : Term)
    (present : Erlang.maps.«get/2» key m = .ok old) :
    (Erlang.maps.«update/3» key value m >>= Erlang.maps.«get/2» key) = .ok value :=
  Erlang.maps.get_after_update m key value old present

theorem update_other_lookup (entries : List (Term × Term)) (key other value old : Term)
    (present : Erlang.maps.«get/2» key (.map entries) = .ok old)
    (distinct : Term.exactCompare other key ≠ .eq) :
    (Erlang.maps.«update/3» key value (.map entries) >>= Erlang.maps.«get/2» other) =
      Erlang.maps.«get/2» other (.map entries) :=
  Erlang.maps.get_after_update_other entries key other value old present distinct

theorem is_map_guard (entries : List (Term × Term)) :
    Erlang.erlang.«is_map/1» (.map entries) = .ok Term.true ∧
    Erlang.erlang.«is_map/1» one = .ok Term.false := ⟨rfl, rfl⟩

end LynxTest.Modules.Maps

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.maps
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Maps
