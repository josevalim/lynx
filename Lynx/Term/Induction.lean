import Lynx.Term.DataTypes

namespace Lynx

/-- Structural induction with elementwise hypotheses for tuples and map bindings. -/
@[induction_eliminator] protected theorem Term.induct {motive : Term → Prop} (t : Term)
    (integer : ∀ n, motive (.integer n))
    (atom : ∀ s, motive (.atom s))
    (tuple : ∀ xs, (∀ x ∈ xs, motive x) → motive (.tuple xs))
    (map : ∀ entries, (∀ k v, (k, v) ∈ entries → motive k ∧ motive v) →
      motive (.map entries))
    (nil : motive .nil)
    (cons : ∀ x xs, motive x → motive xs → motive (.cons x xs)) : motive t := by
  refine Term.rec (motive_2 := fun xs => ∀ x ∈ xs, motive x)
    (motive_3 := fun entries => ∀ k v, (k, v) ∈ entries → motive k ∧ motive v)
    (motive_4 := fun xs => ∀ x ∈ xs, motive x)
    (motive_5 := fun entry => motive entry.1 ∧ motive entry.2)
    integer atom tuple map nil cons ?_ ?_ ?_ ?_ ?_ ?_ t
  · intro xs ih x hx
    exact ih x (by simpa using hx)
  · simp
  · intro entry entries ih ihs k v h
    rcases List.mem_cons.mp h with h | h
    · cases h; exact ih
    · exact ihs k v h
  · simp
  · intro x xs ihx ihxs y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ihx
    · exact ihxs y hy
  · intro k v hk hv; exact ⟨hk, hv⟩

end Lynx
