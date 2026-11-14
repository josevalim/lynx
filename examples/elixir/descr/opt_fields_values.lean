namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Fields of optimized operations, on points whose tuples are tuples of values. -/

theorem opt_union4_eq (d : Dispatcher) {name : String}
    (h : name = "bitmap" ∨ name = "atom" ∨ name = "fun" ∨ name = "list") (x y S : Term) :
    Elixir.Module.Types.Descr.«opt_union/4» d (.atom name) x y S =
      Elixir.Module.Types.Descr.«bare_union/3» d (.atom name) x y := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem opt_diff4_eq (n : Nat) {name t x : Term} (h : name = .atom "bitmap" ∨ name = .atom "atom" ∨ name = .atom "fun")
    (S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/4» (D n) name t x S =
      Elixir.Module.Types.Descr.«bare_difference/3» (D n) name t x := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem opt_inter4_eq (n : Nat) {name x y : Term} (h : name = .atom "bitmap" ∨ name = .atom "atom" ∨ name = .atom "fun")
    (S : Term) :
    Elixir.Module.Types.Descr.«opt_intersection/4» (D n) name x y S =
      Elixir.Module.Types.Descr.«bare_intersection/3» (D n) name x y := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- A type is a subtype of another when each field holds less on points of values. -/

theorem opt_inter_lookup (depth : Nat) (L R : List (Term × Term)) (seen : Term)
    (sL : mapLookup L (.atom "dynamic") = Option.none) (sR : mapLookup R (.atom "dynamic") = Option.none)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ w, Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) q x y seen = .ok w) :
    ∃ I, Elixir.Module.Types.Descr.«opt_intersection/3» (D (depth + 1)) (.map L) (.map R) seen = .ok (.map I) ∧
      (∀ name, (mapLookup L (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
        (mapLookup R (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
        (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
          Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) (.atom name) x y seen = .ok w →
          mapLookup I (.atom name) = if kept (.atom name, w) then some w else Option.none)) ∧
      ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) k₀ v₁ v₂ seen with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y w, Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) q x y seen = .ok w → g q x y = w := by
    intro q x y w run; simp [g, run]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (depth + 1)) "Elixir.Module.Types.Descr"
    "-opt_intersection/3-anonymous-0-" #[seen] L R g (by
      intro e member y hy
      obtain ⟨w, run⟩ := calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/3-anonymous-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-opt_intersection/3-anonymous-0-/4»]
      rw [run, value _ _ _ _ run])
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (depth + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  refine ⟨out, ?_, fun name => ?_, fun q h => ?_⟩
  · unfold Elixir.Module.Types.Descr.«opt_intersection/3»
    simp [getMapKeys_single, sL, sR]
    unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  rotate_left
  · rw [lookO] at h
    cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [hit] at h; cases h
    | some e =>
      obtain ⟨-, hI⟩ := find_entry hit
      rw [lookI] at hI
      cases hitL : (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | none => rw [hitL] at hI; cases hI
      | some f => rw [(find_entry hitL).2]; rfl
  have look : mapLookup out (.atom name) =
      match mapLookup L (.atom name), mapLookup R (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    rw [lookO, find_atom, lookI, find_atom]
    rcases hL : mapLookup L (.atom name) with _ | x <;> rcases hR : mapLookup R (.atom name) with _ | y <;>
      simp [hR]
  refine ⟨fun hL => by rw [look, hL], fun hR => by rw [look, hR]; cases mapLookup L (.atom name) <;> rfl,
    fun x y w hL hR run => by rw [look, hL, hR]; simp only [value _ _ _ _ run]⟩

end Elixir.STTDescrProofsTest
