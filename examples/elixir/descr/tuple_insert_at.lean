namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple_insert_at/3` checks static element types right away. -/
theorem insert_at_static (d : Dispatcher) (X : List (Term × Term)) (i : Nat) {x : Term}
    (sx : x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«tuple_insert_at/3» d (.map X) (.integer i) x =
      Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» d (.map X) (.integer i) x := by
  rcases sx with rfl | ⟨Z, rfl, sZ⟩
  · rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
    simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
      Elixir.Module.Types.Descr.«unfolded_term/0», Erlang.maps.«take/2», mapLookup]
  · rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
    simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
      Erlang.maps.«take/2», sZ]

theorem insert_at_neg (d : Dispatcher) (X : List (Term × Term)) (x : Term) {z : Int} (h : z < 0) :
    Elixir.Module.Types.Descr.«tuple_insert_at/3» d (.map X) (.integer z) x = .ok (.atom "badindex") := by
  have : ¬0 ≤ z := by omega
  rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
  simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare, this]

theorem insert_at_term (d : Dispatcher) (i x : Term) :
    Elixir.Module.Types.Descr.«tuple_insert_at/3» d (.atom "term") i x = .ok (.atom "badtuple") := by
  rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
  rfl

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `equal?/2` holds on element types with the same values. -/
theorem elem_equal (ef : EF nd E V den tl K) {a b : Term} (ha : E a) (hb : E b) (h : ∀ v, den a v ↔ den b v) {m : Nat}
    (hm : K ≤ m) : Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  have s₁ := ef.subc ha hb (fun v => (h v).mp) m hm
  have s₂ := ef.subc hb ha (fun v => (h v).mpr) m hm
  simp only [Elixir.Module.Types.Descr.«equal?/2», s₁, s₂, Lynx.Except.orElse, Lynx.Except.andAlso, Erlang.erlang.«==/2»]
  split <;> simp_all

end

end Elixir.STTDescrProofsTest.Nest
