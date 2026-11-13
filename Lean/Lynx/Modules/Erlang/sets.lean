module

public import Lynx.Term

public section

/-! Version 2 sets are maps from their elements to `[]`. Sets are always
created as version 2 sets, whatever version the options ask for, and set
operations are modeled on those maps directly, rather than through the
iteration strategies OTP picks by size. Version 1 sets and maps holding other
values are not modeled, so operations on them do not return. -/

namespace Erlang.sets
open Lynx

/-- The elements of a version 2 set, when the map holds `[]` for each of them. -/
@[expose] def elements? : Term → Option (List (Term × Term))
  | .map entries =>
    if (Term.mapEntries entries).all (fun entry => entry.2 matches .nil) then some entries else none
  | _ => none

@[expose] def «new/0» : Except Exception Term := .ok (.map [])

/-- The options are ignored, so the set is a version 2 set. -/
@[expose] def «new/1» (_options : Term) : Except Exception Term := .ok (.map [])

@[expose] def «from_list/1» (list : Term) : Except Exception Term :=
  match Term.properList? list with
  | some elements => .ok (.map (elements.map (·, .nil)))
  | none => .error (.error (.atom "badarg"))

/-- The options are ignored, so the set is a version 2 set. -/
@[expose] def «from_list/2» (list _options : Term) : Except Exception Term := «from_list/1» list

@[expose] def «is_element/2» (element set : Term) : Except Exception Term :=
  match set with
  | .map entries => .ok (if (Term.mapLookup entries element).isSome then Term.true else Term.false)
  | _ => .error .exhausted

/-- The number of distinct keys, as `map_size/1` counts them. -/
@[expose] def «size/1» (set : Term) : Except Exception Term :=
  match set with
  | .map entries => .ok (.integer
      ((entries.map Prod.fst).eraseDupsBy (fun a b => Term.compareExact (Term.fuel a b) a b == .eq)).length)
  | _ => .error .exhausted

@[expose] def «union/2» (left right : Term) : Except Exception Term :=
  match elements? left, elements? right with
  | some l, some r => .ok (.map (r ++ l))
  | _, _ => .error .exhausted

@[expose] def «intersection/2» (left right : Term) : Except Exception Term :=
  match elements? left, elements? right with
  | some l, some r =>
    .ok (.map (((Term.mapEntries l).filter fun entry => (Term.mapLookup r entry.1).isSome).map
      fun entry => (entry.1, .nil)))
  | _, _ => .error .exhausted

@[expose] def «subtract/2» (left right : Term) : Except Exception Term :=
  match elements? left, elements? right with
  | some l, some r =>
    .ok (.map (((Term.mapEntries l).filter fun entry => !(Term.mapLookup r entry.1).isSome).map
      fun entry => (entry.1, .nil)))
  | _, _ => .error .exhausted

@[expose] def «is_subset/2» (left right : Term) : Except Exception Term :=
  match left, right with
  | .map l, .map r =>
    .ok (if (Term.mapEntries l).all (fun entry => (Term.mapLookup r entry.1).isSome) then Term.true
      else Term.false)
  | _, _ => .error .exhausted

private theorem lookup_filter (es : List (Term × Term))
    (distinct : es.Pairwise (fun a b => Term.compareExact (Term.fuel a.1 b.1) a.1 b.1 ≠ .eq))
    (keep : Term × Term → Bool) (query : Term) :
    (Term.mapLookup ((es.filter keep).map fun entry => (entry.1, Term.nil)) query).isSome =
      match es.find? (fun e => decide (Term.compareExact (Term.fuel query e.1) query e.1 = .eq)) with
      | some e => keep e
      | none => false := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have tail := ih (List.pairwise_cons.mp distinct).2
    by_cases same : Term.compareExact (Term.fuel query e.1) query e.1 = .eq
    · have absent : rest.find? (fun p => decide (Term.compareExact (Term.fuel query p.1) query p.1 = .eq)) = none := by
        rw [List.find?_eq_none]
        intro p mp hit
        exact (List.pairwise_cons.mp distinct).1 p mp
          (Term.compareExact_eq_trans (Term.compareExact_eq_symm same) (of_decide_eq_true hit))
      rw [absent] at tail
      cases hk : keep e <;> simp_all [Term.mapLookup]
      intro a b m _
      exact absent a b m
    · cases hk : keep e <;> simp_all [Term.mapLookup]

private theorem member_filter (entries : List (Term × Term)) (keep : Term → Bool)
    (congr : ∀ a b, Term.compareExact (Term.fuel a b) a b = .eq → keep a = keep b) (query : Term) :
    (Term.mapLookup (((Term.mapEntries entries).filter fun entry => keep entry.1).map
        fun entry => (entry.1, Term.nil)) query).isSome =
      ((Term.mapLookup entries query).isSome && keep query) := by
  rw [lookup_filter _ (Term.mapEntries_distinct entries), ← Term.mapLookup_mapEntries]
  simp only [Term.mapLookup]
  cases found : (Term.mapEntries entries).find? (fun e => decide (Term.compareExact (Term.fuel query e.1) query e.1 = .eq)) with
  | none => rfl
  | some e =>
    have same : Term.compareExact (Term.fuel query e.1) query e.1 = .eq := by simpa using List.find?_some found
    simp [congr _ _ same]

/-- A map is a version 2 set when it holds [] for each of its keys. -/
theorem elements_iff (entries : List (Term × Term)) :
    elements? (.map entries) = some entries ↔
      ∀ key value, Term.mapLookup entries key = some value → value = .nil := by
  constructor
  · intro set key value found
    simp only [elements?] at set
    split at set
    · rename_i all
      rw [← Term.mapLookup_mapEntries] at found
      simp only [Term.mapLookup, Option.map_eq_some_iff] at found
      obtain ⟨entry, hit, rfl⟩ := found
      have := List.all_eq_true.mp all entry (List.mem_of_find?_eq_some hit)
      cases h : entry.2 <;> simp_all
    · cases set
  · intro nil
    simp only [elements?]
    refine ite_eq_left (List.all_eq_true.mpr fun entry member => ?_)
    simp [nil _ _ (Term.mapLookup_of_mem_mapEntries member)]

private theorem eq_of_elements {set : Term} {entries : List (Term × Term)}
    (found : elements? set = some entries) : set = .map entries := by
  cases set <;> simp only [elements?, reduceCtorEq] at found
  split at found <;> simp_all

private theorem elements_nil (keys : List (Term × Term)) :
    elements? (.map (keys.map fun entry => (entry.1, Term.nil))) =
      some (keys.map fun entry => (entry.1, Term.nil)) := by
  rw [elements_iff]
  intro key value found
  simp only [Term.mapLookup, Option.map_eq_some_iff] at found
  obtain ⟨entry, hit, rfl⟩ := found
  have := List.mem_of_find?_eq_some hit
  simp only [List.mem_map] at this
  obtain ⟨_, _, rfl⟩ := this
  rfl

/-- An element belongs to a union when it belongs to either set. -/
theorem union_member (left right : Term) (l r : List (Term × Term))
    (hl : elements? left = some l) (hr : elements? right = some r) :
    ∃ entries, «union/2» left right = .ok (.map entries) ∧ elements? (.map entries) = some entries ∧
      ∀ element, (Term.mapLookup entries element).isSome =
        ((Term.mapLookup l element).isSome || (Term.mapLookup r element).isSome) := by
  have setL := (elements_iff l).mp (eq_of_elements hl ▸ hl)
  have setR := (elements_iff r).mp (eq_of_elements hr ▸ hr)
  refine ⟨r ++ l, by simp [«union/2», hl, hr], (elements_iff _).mpr fun key value found => ?_,
    fun element => ?_⟩
  · simp only [Term.mapLookup, List.find?_append, Option.map_or] at found
    cases hit : r.find? (fun entry => decide (Term.compareExact (Term.fuel key entry.1) key entry.1 = .eq)) with
    | none => exact setL key value (by simpa [Term.mapLookup, hit] using found)
    | some entry => exact setR key value (by simpa [Term.mapLookup, hit] using found)
  · simp only [Term.mapLookup, List.find?_append, Option.map_or]
    cases (r.find? fun entry => decide (Term.compareExact (Term.fuel element entry.1) element entry.1 = .eq)) <;> simp [Bool.or_comm]

/-- An element belongs to an intersection when it belongs to both sets. -/
theorem intersection_member (left right : Term) (l r : List (Term × Term))
    (hl : elements? left = some l) (hr : elements? right = some r) :
    ∃ entries, «intersection/2» left right = .ok (.map entries) ∧
      elements? (.map entries) = some entries ∧
      ∀ element, (Term.mapLookup entries element).isSome =
        ((Term.mapLookup l element).isSome && (Term.mapLookup r element).isSome) := by
  refine ⟨((Term.mapEntries l).filter fun entry => (Term.mapLookup r entry.1).isSome).map
    fun entry => (entry.1, .nil), by simp only [«intersection/2», hl, hr], elements_nil _,
    fun element => ?_⟩
  exact member_filter l (fun key => (Term.mapLookup r key).isSome)
    (fun a b same => by rw [Term.mapLookup_congr same]) element

/-- An element belongs to a difference when it belongs to the first set only. -/
theorem subtract_member (left right : Term) (l r : List (Term × Term))
    (hl : elements? left = some l) (hr : elements? right = some r) :
    ∃ entries, «subtract/2» left right = .ok (.map entries) ∧
      elements? (.map entries) = some entries ∧
      ∀ element, (Term.mapLookup entries element).isSome =
        ((Term.mapLookup l element).isSome && !(Term.mapLookup r element).isSome) := by
  refine ⟨((Term.mapEntries l).filter fun entry => !(Term.mapLookup r entry.1).isSome).map
    fun entry => (entry.1, .nil), by simp only [«subtract/2», hl, hr], elements_nil _,
    fun element => ?_⟩
  exact member_filter l (fun key => !(Term.mapLookup r key).isSome)
    (fun a b same => by rw [Term.mapLookup_congr same]) element

/-- Sets created from lists are version 2 sets of the listed elements. -/
theorem from_list_elements (elements : List Term) :
    ∃ entries, «from_list/1» (Term.list elements) = .ok (.map entries) ∧
      elements? (.map entries) = some entries ∧
      ∀ element, (Term.mapLookup entries element).isSome ↔
        ∃ x ∈ elements, Term.compareExact (Term.fuel element x) element x = .eq := by
  refine ⟨elements.map (·, .nil), by simp [«from_list/1»], ?_, fun element => ?_⟩
  · have values : ∀ entry ∈ Term.mapEntries (elements.map (·, Term.nil)), entry.2 = .nil := by
      intro entry member
      have := Term.mem_of_mem_mapEntries member
      simp at this
      obtain ⟨x, -, rfl⟩ := this
      rfl
    have all : (Term.mapEntries (elements.map (·, Term.nil))).all (fun entry => entry.2 matches .nil) := by
      rw [List.all_eq_true]
      intro entry member
      rw [values entry member]
    simp only [elements?]
    exact ite_eq_left all
  · rw [Term.mapLookup_isSome]
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, member, rfl⟩, same⟩
      exact ⟨x, member, same⟩
    · rintro ⟨x, member, same⟩
      exact ⟨(x, .nil), ⟨x, member, rfl⟩, same⟩

private theorem loop_length (r : Term → Term → Bool) (as bs : List Term) :
    bs.length ≤ (List.eraseDupsBy.loop r as bs).length := by
  induction as generalizing bs with
  | nil => simp [List.eraseDupsBy.loop]
  | cons a rest ih =>
    simp only [List.eraseDupsBy.loop]
    split
    · exact ih bs
    · exact Nat.le_trans (Nat.le_succ _) (ih (a :: bs))

/-- Sets of size zero have no elements. -/
theorem size_empty (entries : List (Term × Term)) (element : Term)
    (empty : «size/1» (.map entries) = .ok (.integer 0)) : Term.mapLookup entries element = none := by
  cases entries with
  | nil => rfl
  | cons entry rest =>
    have := loop_length (fun a b => Term.compareExact (Term.fuel a b) a b == .eq) (rest.map Prod.fst) [entry.1]
    simp only [«size/1», List.map_cons, List.eraseDupsBy, List.eraseDupsBy.loop, List.any_nil,
      Except.ok.injEq, Term.integer.injEq] at empty
    simp at this
    omega

end Erlang.sets
