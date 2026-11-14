namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Merging maps field by field, whatever their keys. -/

/-- The bindings of a map other than its dynamic part, as `maps:remove/2` and `maps:take/2` leave them. -/
def rmDyn (X : List (Term × Term)) : List (Term × Term) :=
  X.filter fun entry => compareExact (fuel (.atom "dynamic") entry.1) (.atom "dynamic") entry.1 != .eq

theorem lookup_rmDyn (X : List (Term × Term)) (q : Term) :
    mapLookup (rmDyn X) q = if compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq then none else mapLookup X q := by
  rw [rmDyn, mapLookup_filter]

theorem lookup_rmDyn_name (X : List (Term × Term)) {name : String} (h : name ≠ "dynamic") :
    mapLookup (rmDyn X) (.atom name) = mapLookup X (.atom name) := by
  simp [lookup_rmDyn, h]

theorem rmDyn_static {X : List (Term × Term)} (h : mapLookup X (.atom "dynamic") = none) : rmDyn X = X := by
  refine List.filter_eq_self.mpr fun e me => ?_
  cases c : compareExact (fuel (.atom "dynamic") e.1) (.atom "dynamic") e.1 <;> simp
  have : (mapLookup X (.atom "dynamic")).isSome := (mapLookup_isSome X _).mpr ⟨e, me, c⟩
  rw [h] at this; cases this

theorem names_ne_dyn {name : String} (h : name ∈ names) : name ≠ "dynamic" := by
  simp [names] at h; rintro rfl; simp at h

/-- Merging maps with atom keys looks up the combined values of shared keys and the others' values. -/
theorem merge_gen (d : Dispatcher) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term)
    (call : ∀ q v₁ v₂, d.pure (.function module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂)
    (L R : List (Term × Term)) (keysR : ∀ q, (mapLookup R q).isSome → ∃ n, q = .atom n)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∃ u, f q x y = .ok u) :
    ∃ U, Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map L) (.map R) (.function module name 3 caps) =
        .ok (.map U) ∧
      ∀ q, (mapLookup R q = none → mapLookup U q = mapLookup L q) ∧
        (∀ y, mapLookup R q = some y → mapLookup L q = none → mapLookup U q = some y) ∧
        (∀ x y u, mapLookup L q = some x → mapLookup R q = some y → f q x y = .ok u → mapLookup U q = some u) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match f k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, f q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
  obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup d module name caps L R g (by
    intro e me x hx
    have hy := mapLookup_of_mem_mapEntries me
    obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
    rw [call, ru, value _ _ _ _ ru])
  refine ⟨out, by simpa using run, fun q => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rfl
    | some e => rw [(find_entry hit).2] at hR; cases hR
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit] at hR; cases hR
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [h] at hR; cases hR
      simp [← mapLookup_congr qe, hL]
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit] at hR; cases hR
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [h] at hR; cases hR
      obtain ⟨n, hn⟩ := keysR e.1 (by rw [← mapLookup_congr qe, h]; rfl)
      rw [hn] at qe
      obtain rfl := (compareExact_eq_atom q n).mp qe
      simp [hn, hL, value _ _ _ _ ru]

/-- Intersecting maps looks up the kept combined values of shared keys. -/
theorem intersect_gen (n : Nat) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term)
    (call : ∀ q v₁ v₂, (D (n + 1)).pure (.function module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂)
    (L R : List (Term × Term)) (keysL : ∀ q, (mapLookup L q).isSome → ∃ n, q = .atom n)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∃ u, f q x y = .ok u) :
    ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (D (n + 1)) (.map L) (.map R) (.function module name 3 caps) =
        .ok (.map I) ∧
      ∀ q, (mapLookup L q = none → mapLookup I q = none) ∧ (mapLookup R q = none → mapLookup I q = none) ∧
        (∀ x y u, mapLookup L q = some x → mapLookup R q = some y → f q x y = .ok u →
          mapLookup I q = if kept (q, u) then some u else none) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match f k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, f q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (n + 1)) module name caps L R g (by
    intro e member y hy
    obtain ⟨w, run⟩ := calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy
    rw [call, run, value _ _ _ _ run])
  have lookI' : ∀ q, mapLookup I q =
      match mapLookup L q, mapLookup R q with
      | some x, some y => some (g q x y)
      | _, _ => none := by
    intro q
    rw [lookI]
    cases hit : (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit]
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      obtain ⟨n, hn⟩ := keysL e.1 (by rw [← mapLookup_congr qe, h]; rfl)
      rw [hn] at qe
      obtain rfl := (compareExact_eq_atom q n).mp qe
      rw [h, ← hn]
      dsimp only
      cases mapLookup R e.1 <;> rfl
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (n + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  refine ⟨out, ?_, fun q => ?_⟩
  · unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  have look : mapLookup out q =
      match mapLookup L q, mapLookup R q with
      | some x, some y => if kept (q, g q x y) then some (g q x y) else none
      | _, _ => none := by
    rw [lookO]
    cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none =>
      have := find_none hit
      rw [lookI'] at this
      revert this
      cases mapLookup L q <;> cases mapLookup R q <;> simp
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [lookI'] at h
      revert h
      cases mapLookup L q <;> cases mapLookup R q <;> simp
      intro h
      simp only [kept]
      rw [h]
      rfl
  refine ⟨fun hL => by rw [look, hL], fun hR => by rw [look, hR]; cases mapLookup L q <;> rfl,
    fun x y w hL hR run => by rw [look, hL, hR]; simp only [value _ _ _ _ run]⟩

end Elixir.STTDescrProofsTest.Nest
