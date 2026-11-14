namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Fusing tuple literals of flat element types. -/

theorem Pairs.refl {R : Term → Term → Prop} (h : ∀ x, R x x) : ∀ l : List Term, Pairs R l l
  | [] => trivial
  | x :: l => ⟨h x, Pairs.refl h l⟩

/-- The number of literals in a BDD, regardless of hashes. -/
def bsize (t : Term) : Nat :=
  match t with
  | .tuple ⟨[_, _, c, u, d]⟩ => 1 + bsize c + bsize u + bsize d
  | .tuple ⟨[_, _, _]⟩ => 1
  | _ => 0
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem bsize_node (h lit c u d : Term) : bsize (.tuple #[h, lit, c, u, d]) = 1 + bsize c + bsize u + bsize d := by
  rw [bsize]

theorem bsize_leaf (k x y : Term) : bsize (.tuple #[k, x, y]) = 1 := by
  rw [bsize]

theorem bsize_atom (s : String) : bsize (.atom s) = 0 := by
  rw [bsize]
  all_goals intros; simp_all

theorem tuple_union_right {x : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) (k : Term) :
    Elixir.Module.Types.Descr.«tuple_union/2» x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil]) := by
  unfold Elixir.Module.Types.Descr.«tuple_union/2»
  split
  · exact (hx _ rfl).elim
  · rename_i e; simp at e; subst e; rfl
  · rename_i h; exact (h _ rfl).elim

end Elixir.STTDescrProofsTest
