module

import Erlang.maps
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

end LynxTest.Modules.Maps

run_cmd do
  LynxTest.ProofAudit.checkModule `Erlang.maps
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Maps
