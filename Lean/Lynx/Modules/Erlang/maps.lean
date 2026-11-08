module

public import Lynx.Term

public section

namespace Erlang.maps
open Lynx

@[expose] def «new/0» : Except Exception Term := .ok (Term.map [])

@[expose] def «get/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    match (entries.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd with
    | some v => .ok v
    | none => .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «put/3» (key value input : Term) : Except Exception Term :=
  match input with
  | .map entries => .ok (.map ((key, value) :: entries))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «update/3» (key value input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    if (entries.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).isSome then
      .ok (.map ((key, value) :: entries))
    else
      .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

/-- The visible bindings as `{Key, Value}` pairs, in the order map generators use. -/
@[expose] def «to_list/1» : Term → Except Exception Term
  | .map entries => .ok (Term.list ((Term.mapEntries entries).map fun entry => .tuple #[entry.1, entry.2]))
  | input => .error (.error (.tuple #[.atom "badmap", input]))

/-- Fold over the visible bindings in the order `to_list/1` returns them.
Iterators fold over their remaining bindings. -/
@[expose] def «fold/3» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (function init input : Term) : m Term :=
  let fold (pairs : List (Term × Term)) :=
    pairs.foldlM (fun acc entry => Dispatch.dispatch dispatcher function #[entry.1, entry.2, acc]) init
  match function with
  | .function _ _ 3 _ =>
    match input with
    | .map entries => fold (Term.mapEntries entries)
    | .atom "none" => pure init
    | .tuple ⟨[key, value, rest]⟩ =>
      match Term.pairList? rest with
      | some pairs => fold ((key, value) :: pairs)
      | none => throw (.error (.atom "badarg"))
    | input =>
      match Term.pairList? input with
      | some pairs => fold pairs
      | none => throw (.error (.tuple #[.atom "badmap", input]))
  | _ => throw (.error (.atom "badarg"))

/-- An iterator over the visible bindings, as a list of `{Key, Value}` pairs in
the order `to_list/1` returns them. The BEAM's iterator representation is opaque. -/
@[expose] def «iterator/1» : Term → Except Exception Term
  | .map entries => .ok (Term.list ((Term.mapEntries entries).map fun entry => .tuple #[entry.1, entry.2]))
  | input => .error (.error (.tuple #[.atom "badmap", input]))

/-- The next binding of an iterator as `{Key, Value, Next}`, or `none`. -/
@[expose] def «next/1» : Term → Except Exception Term
  | .cons (.tuple ⟨[key, value]⟩) rest => .ok (.tuple #[key, value, rest])
  | .nil | .atom "none" => .ok (.atom "none")
  | iterator@(.tuple ⟨[_, _, _]⟩) => .ok iterator
  | _ => .error (.error (.atom "badarg"))

@[expose] def «find/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    match Term.mapLookup entries key with
    | some value => .ok (.tuple #[.atom "ok", value])
    | none => .ok (.atom "error")
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «is_key/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries => .ok (if (Term.mapLookup entries key).isSome then Term.true else Term.false)
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

/-- The visible keys, in the order `to_list/1` returns them. -/
@[expose] def «keys/1» : Term → Except Exception Term
  | .map entries => .ok (Term.list ((Term.mapEntries entries).map Prod.fst))
  | input => .error (.error (.tuple #[.atom "badmap", input]))

/-- The visible values, in the order `to_list/1` returns them. -/
@[expose] def «values/1» : Term → Except Exception Term
  | .map entries => .ok (Term.list ((Term.mapEntries entries).map Prod.snd))
  | input => .error (.error (.tuple #[.atom "badmap", input]))

/-- Every binding of the key is removed, including shadowed ones. -/
@[expose] def «remove/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries => .ok (.map (entries.filter fun entry => Term.exactCompare key entry.1 != .eq))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «take/2» (key input : Term) : Except Exception Term :=
  match input with
  | .map entries =>
    match Term.mapLookup entries key with
    | some value =>
      .ok (.tuple #[value, .map (entries.filter fun entry => Term.exactCompare key entry.1 != .eq)])
    | none => .ok (.atom "error")
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[expose] def «from_keys/2» (keys value : Term) : Except Exception Term :=
  match Term.properList? keys with
  | some keys => .ok (.map (keys.map (·, value)))
  | none => .error (.error (.atom "badarg"))

/-- Combine the values of keys in both maps with `Combiner(Key, Value1, Value2)`,
keeping the other bindings of either map. The order of the calls is unspecified. -/
@[expose] def «merge_with/3» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (combiner left right : Term) : m Term :=
  match combiner, left, right with
  | .function _ _ 3 _, .map l, .map r => do
    let combined ← (Term.mapEntries r).mapM fun entry =>
      match Term.mapLookup l entry.1 with
      | some value => (entry.1, ·) <$> Dispatch.dispatch dispatcher combiner #[entry.1, value, entry.2]
      | none => pure entry
    pure (.map (combined ++ l))
  | .function _ _ 3 _, .map _, _ => throw (.error (.tuple #[.atom "badmap", right]))
  | .function _ _ 3 _, _, _ => throw (.error (.tuple #[.atom "badmap", left]))
  | _, _, _ => throw (.error (.atom "badarg"))

/-- Combine the values of keys in both maps with `Combiner(Key, Value1, Value2)`,
dropping keys in only one of them. The order of the calls is unspecified. -/
@[expose] def «intersect_with/3» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (combiner left right : Term) : m Term :=
  match combiner, left, right with
  | .function _ _ 3 _, .map l, .map r => do
    let combined ← (Term.mapEntries l).mapM fun entry =>
      match Term.mapLookup r entry.1 with
      | some value =>
        (fun result => some (entry.1, result)) <$>
          Dispatch.dispatch dispatcher combiner #[entry.1, entry.2, value]
      | none => pure none
    pure (.map combined.reduceOption)
  | .function _ _ 3 _, .map _, _ => throw (.error (.tuple #[.atom "badmap", right]))
  | .function _ _ 3 _, _, _ => throw (.error (.tuple #[.atom "badmap", left]))
  | _, _, _ => throw (.error (.atom "badarg"))

/-- Keep the bindings for which `Pred(Key, Value)` returns `true`. Maps and the
iterators of `iterator/1` are filtered in the order `to_list/1` returns them. -/
@[expose] def «filter/2» {m : Type → Type u} [Monad m] [MonadExceptOf Exception m] [Dispatch m]
    (dispatcher : Dispatcher) (predicate input : Term) : m Term :=
  let keep (pairs : List (Term × Term)) : m Term := do
    let kept ← pairs.mapM fun entry => do
      match ← Dispatch.dispatch dispatcher predicate #[entry.1, entry.2] with
      | .atom "true" => pure (some entry)
      | .atom "false" => pure none
      | other => throw (.error (.tuple #[.atom "case_clause", other]))
    pure (.map kept.reduceOption)
  match predicate with
  | .function _ _ 2 _ =>
    match input with
    | .map entries => keep (Term.mapEntries entries)
    | .atom "none" => pure (.map [])
    | .tuple ⟨[key, value, rest]⟩ =>
      match Term.pairList? rest with
      | some pairs => keep ((key, value) :: pairs)
      | none => throw (.error (.tuple #[.atom "badmap", input]))
    | input =>
      match Term.pairList? input with
      | some pairs => keep pairs
      | none => throw (.error (.tuple #[.atom "badmap", input]))
  | _ => throw (.error (.atom "badarg"))

/-- Later pairs take precedence, so they shadow earlier ones. -/
@[expose] def «from_list/1» (list : Term) : Except Exception Term :=
  match Term.pairList? list with
  | some entries => .ok (.map entries.reverse)
  | none => .error (.error (.atom "badarg"))

@[expose] def «merge/2» (left right : Term) : Except Exception Term :=
  match left, right with
  | .map a, .map b => .ok (.map (b ++ a))
  | .map _, _ => .error (.error (.tuple #[.atom "badmap", right]))
  | _, _ => .error (.error (.tuple #[.atom "badmap", left]))

/-- Lookup after merging prefers the right map, falling back to the left
when the key is absent. -/
theorem get_merge (key : Term) (left right : List (Term × Term)) :
    («merge/2» (.map left) (.map right) >>= «get/2» key) =
      match «get/2» key (.map right) with
      | .error _ => «get/2» key (.map left)
      | result => result := by
  simp only [«merge/2», Except.ok_bind, «get/2», List.find?_append, Option.map_or]
  cases (right.find? fun e => decide (Term.exactCompare key e.1 = .eq)).map Prod.snd <;> rfl

/-- Maps with identical lookup results are semantically equal. -/
theorem compare_eq_of_get (left right : List (Term × Term))
    (h : ∀ key, «get/2» key (.map left) = «get/2» key (.map right)) :
    Term.compare (.map left) (.map right) = .eq := by
  apply Term.map_compare_eq_of_lookup
  intro key
  have equal := h key
  simp only [«get/2»] at equal
  change Option.Rel _
    ((left.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd)
    ((right.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd)
  cases ha : (left.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd <;>
    cases hb : (right.find? fun entry => decide (Term.exactCompare key entry.1 = .eq)).map Prod.snd <;> simp_all

/-- Map shape is the only requirement; keys and values may be arbitrary terms. -/
theorem get_after_put (m k v : Term)
    (hm : ∃ entries, m = .map entries) :
    («put/3» k v m >>= «get/2» k) = .ok v := by
  obtain ⟨entries, rfl⟩ := hm
  simp [«put/3», «get/2»]

/-- Updating a present key has the same result as putting it. -/
@[simp] theorem update_eq_put_of_get (m k v old : Term)
    (present : «get/2» k m = .ok old) :
    «update/3» k v m = «put/3» k v m := by
  cases m <;> simp [«get/2»] at present
  rename_i entries
  cases found : entries.find? (fun entry => decide (Term.exactCompare k entry.1 = .eq)) <;>
    simp_all [«update/3», «put/3»]

/-- A missing key raises badkey. -/
@[simp] theorem update_missing (entries : List (Term × Term)) (k v : Term)
    (missing : «get/2» k (.map entries) = .error (.error (.tuple #[.atom "badkey", k]))) :
    «update/3» k v (.map entries) = .error (.error (.tuple #[.atom "badkey", k])) := by
  cases found : entries.find? (fun entry => decide (Term.exactCompare k entry.1 = .eq)) <;>
    simp [«get/2», «update/3», found] at missing ⊢

/-- Reading the updated key returns its new value. -/
theorem get_after_update (m k v old : Term) (present : «get/2» k m = .ok old) :
    («update/3» k v m >>= «get/2» k) = .ok v := by
  rw [update_eq_put_of_get m k v old present]
  cases m <;> simp [«get/2»] at present
  apply get_after_put
  exact ⟨_, rfl⟩

/-- Putting a distinct key preserves lookup. -/
theorem get_after_put_other (entries : List (Term × Term)) (key other value : Term)
    (distinct : Term.exactCompare other key ≠ .eq) :
    («put/3» key value (.map entries) >>= «get/2» other) = «get/2» other (.map entries) := by
  simp [«put/3», «get/2», distinct]

/-- Updating a present key preserves lookup at distinct keys. -/
theorem get_after_update_other (entries : List (Term × Term)) (key other value old : Term)
    (present : «get/2» key (.map entries) = .ok old)
    (distinct : Term.exactCompare other key ≠ .eq) :
    («update/3» key value (.map entries) >>= «get/2» other) = «get/2» other (.map entries) := by
  rw [update_eq_put_of_get (.map entries) key value old present]
  exact get_after_put_other entries key other value distinct

/-- Right-biased map merge is associative. -/
theorem merge_associative (a b c : Term)
    (ha : ∃ entries, a = .map entries)
    (hb : ∃ entries, b = .map entries)
    (hc : ∃ entries, c = .map entries) :
    («merge/2» a b >>= fun ab => «merge/2» ab c) =
      («merge/2» b c >>= «merge/2» a) := by
  obtain ⟨left, rfl⟩ := ha
  obtain ⟨middle, rfl⟩ := hb
  obtain ⟨right, rfl⟩ := hc
  simp [«merge/2»]

private theorem mapM_ok {α β : Type} (f : α → Except Exception β) (h : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (h x)) → xs.mapM f = .ok (xs.map h)
  | [], _ => rfl
  | x :: xs, all => by
    simp [List.mapM_cons, all x (by simp), mapM_ok f h xs (fun y my => all y (by simp [my]))]

private theorem lookup_append_map (es l : List (Term × Term)) (H : Term × Term → Term) (q : Term) :
    Term.mapLookup ((es.map fun e => (e.1, H e)) ++ l) q =
      match es.find? (fun e => decide (Term.exactCompare q e.1 = .eq)) with
      | some e => some (H e)
      | none => Term.mapLookup l q := by
  simp only [Term.mapLookup, List.find?_append, List.find?_map]
  dsimp only [Function.comp_def]
  cases es.find? (fun e => decide (Term.exactCompare q e.1 = .eq)) <;> rfl

private theorem lookup_reduceOption_absent (es : List (Term × Term)) (F : Term × Term → Option Term)
    (q : Term) (absent : ∀ p ∈ es, Term.exactCompare q p.1 ≠ .eq) :
    Term.mapLookup ((es.map fun e => (F e).map fun v => (e.1, v)).reduceOption) q = none := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have miss := absent e (by simp)
    have rest' := ih fun p mp => absent p (by simp [mp])
    cases hF : F e <;> simp_all [List.reduceOption, Term.mapLookup]

private theorem lookup_reduceOption (es : List (Term × Term))
    (distinct : es.Pairwise (fun a b => Term.exactCompare a.1 b.1 ≠ .eq)) (F : Term × Term → Option Term)
    (q : Term) :
    Term.mapLookup ((es.map fun e => (F e).map fun v => (e.1, v)).reduceOption) q =
      match es.find? (fun e => decide (Term.exactCompare q e.1 = .eq)) with
      | some e => F e
      | none => none := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have tail := ih (List.pairwise_cons.mp distinct).2
    by_cases same : Term.exactCompare q e.1 = .eq
    · have absent : ∀ p ∈ rest, Term.exactCompare q p.1 ≠ .eq := fun p mp hit =>
        (List.pairwise_cons.mp distinct).1 p mp
          (Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm same) hit)
      have none := lookup_reduceOption_absent rest F q absent
      cases hF : F e <;> simp_all [List.reduceOption, Term.mapLookup]
    · cases hF : F e <;> simp_all [List.reduceOption, Term.mapLookup]

/-- When the combiner returns `g Key Value1 Value2`, merged keys take the combined
value, and other keys keep their value in either map. -/
theorem merge_with_lookup (dispatcher : Dispatcher) (module name : String) (captures : Array Term)
    (l r : List (Term × Term)) (g : Term → Term → Term → Term)
    (calls : ∀ entry ∈ Term.mapEntries r, ∀ value, Term.mapLookup l entry.1 = some value →
      dispatcher.pure (.function module name 3 captures) #[entry.1, value, entry.2] = .ok (g entry.1 value entry.2)) :
    ∃ out, («merge_with/3» dispatcher (.function module name 3 captures) (.map l) (.map r) :
        Except Exception Term) = .ok (.map out) ∧
      ∀ q, Term.mapLookup out q =
        match (Term.mapEntries r).find? (fun e => decide (Term.exactCompare q e.1 = .eq)) with
        | some e => some (match Term.mapLookup l e.1 with | some v => g e.1 v e.2 | none => e.2)
        | none => Term.mapLookup l q := by
  let H : Term × Term → Term := fun e =>
    match Term.mapLookup l e.1 with | some v => g e.1 v e.2 | none => e.2
  have run := mapM_ok (fun entry => match Term.mapLookup l entry.1 with
      | some value => (entry.1, ·) <$> dispatcher.pure (.function module name 3 captures) #[entry.1, value, entry.2]
      | none => pure entry) (fun e => (e.1, H e)) (Term.mapEntries r) (by
    intro e me
    cases hl : Term.mapLookup l e.1 with
    | none => simp [hl, H]
    | some v => simp only [hl, H, calls e me v hl]; rfl)
  refine ⟨_, ?_, fun q => lookup_append_map _ l H q⟩
  simp only [«merge_with/3», Dispatch.dispatch]
  rw [run]
  rfl

/-- When the combiner returns `g Key Value1 Value2`, shared keys take the combined
value, and keys in only one map are dropped. -/
theorem intersect_with_lookup (dispatcher : Dispatcher) (module name : String) (captures : Array Term)
    (l r : List (Term × Term)) (g : Term → Term → Term → Term)
    (calls : ∀ entry ∈ Term.mapEntries l, ∀ value, Term.mapLookup r entry.1 = some value →
      dispatcher.pure (.function module name 3 captures) #[entry.1, entry.2, value] = .ok (g entry.1 entry.2 value)) :
    ∃ out, («intersect_with/3» dispatcher (.function module name 3 captures) (.map l) (.map r) :
        Except Exception Term) = .ok (.map out) ∧
      ∀ q, Term.mapLookup out q =
        match (Term.mapEntries l).find? (fun e => decide (Term.exactCompare q e.1 = .eq)) with
        | some e => (Term.mapLookup r e.1).map (g e.1 e.2)
        | none => none := by
  let F : Term × Term → Option Term := fun e => (Term.mapLookup r e.1).map (g e.1 e.2)
  have run := mapM_ok (fun entry => match Term.mapLookup r entry.1 with
      | some value => (fun result => some (entry.1, result)) <$>
          dispatcher.pure (.function module name 3 captures) #[entry.1, entry.2, value]
      | none => pure none) (fun e => (F e).map fun v => (e.1, v)) (Term.mapEntries l) (by
    intro e me
    cases hr : Term.mapLookup r e.1 with
    | none => simp [hr, F]
    | some v => simp only [hr, F, calls e me v hr]; rfl)
  refine ⟨_, ?_, fun q => lookup_reduceOption _ (Term.mapEntries_distinct l) F q⟩
  simp only [«intersect_with/3», Dispatch.dispatch]
  rw [run]
  rfl

/-- When the predicate decides each binding by `keep`, the bindings it keeps remain. -/
theorem filter_lookup (dispatcher : Dispatcher) (module name : String) (captures : Array Term)
    (entries : List (Term × Term)) (keep : Term × Term → Bool)
    (calls : ∀ entry ∈ Term.mapEntries entries,
      dispatcher.pure (.function module name 2 captures) #[entry.1, entry.2] =
        .ok (if keep entry then Term.true else Term.false)) :
    ∃ out, («filter/2» dispatcher (.function module name 2 captures) (.map entries) :
        Except Exception Term) = .ok (.map out) ∧
      ∀ q, Term.mapLookup out q =
        match (Term.mapEntries entries).find? (fun e => decide (Term.exactCompare q e.1 = .eq)) with
        | some e => if keep e then some e.2 else none
        | none => none := by
  let F : Term × Term → Option Term := fun e => if keep e then some e.2 else none
  refine ⟨_, ?_, fun q => lookup_reduceOption _ (Term.mapEntries_distinct entries) F q⟩
  simp only [«filter/2», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => (F e).map fun v => (e.1, v)) _ ?all]
  · rfl
  · intro e me
    cases hk : keep e <;> simp [calls e me, hk, F, Term.true, Term.false]

end Erlang.maps
