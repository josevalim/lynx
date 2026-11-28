module
public import Lynx
public section

namespace ShuffleProof
open Lynx

/-- Prepend elements onto a term, as the shuffle prepends onto its accumulator. -/
@[expose] def onto : List Term → Term → Term
  | [], acc => acc
  | x :: xs, acc => .cons x (onto xs acc)

@[simp] theorem onto_nil (acc : Term) : onto [] acc = acc := rfl
@[simp] theorem onto_cons (x : Term) (xs : List Term) (acc : Term) :
    onto (x :: xs) acc = .cons x (onto xs acc) := rfl
@[simp] theorem onto_list (xs : List Term) : onto xs .nil = Term.list xs := by
  induction xs <;> simp_all

theorem onto_append (xs ys : List Term) (acc : Term) :
    onto (xs ++ ys) acc = onto xs (onto ys acc) := by
  induction xs <;> simp_all

/-- Split a successful return into the paths that produce it, discarding those
that raise. The values bound along the way are split the same way. -/
syntax "peel " ident : tactic
macro_rules
  | `(tactic| peel $h:ident) => `(tactic| repeat' (first
    | contradiction
    | (subst $h:ident)
    | (simp only [Lynx.Except.tryWith, Lynx.Except.bind_eq_ok, Lynx.Except.pure_eq_ok,
        Except.ok.injEq] at $h:ident)
    | (obtain ⟨_, bound, $h:ident⟩ := $h:ident; peel bound)
    | (split at $h:ident)))

/-- The shuffle of three elements returns one of their orders. -/
theorem perm3 (x y z : Term) :
    [z, y, x].Perm [x, y, z] ∧ [y, z, x].Perm [x, y, z] ∧ [z, x, y].Perm [x, y, z] ∧
      [x, z, y].Perm [x, y, z] ∧ [y, x, z].Perm [x, y, z] := by
  have yzx : [y, z, x].Perm [x, y, z] :=
    ((List.Perm.swap x z []).cons y).trans (List.Perm.swap x y [z])
  have xzy : [x, z, y].Perm [x, y, z] := (List.Perm.swap y z []).cons x
  exact ⟨(List.Perm.swap y z [x]).trans yzx, yzx, (List.Perm.swap x z [y]).trans xzy, xzy,
    List.Perm.swap x y [z]⟩

theorem nil_eq_list {l : List Term} (same : Term.nil = Term.list l) : l = [] := by
  cases l <;> simp_all

theorem cons_eq_list {x tail : Term} {l : List Term} (same : Term.cons x tail = Term.list l) :
    ∃ rest, l = x :: rest ∧ tail = Term.list rest := by
  cases l <;> simp_all

/-- An element moved from a bucket to the front keeps the permutation. -/
theorem move (xs before after : List Term) (x : Term) :
    (xs ++ before ++ x :: after).Perm (x :: xs ++ before ++ after) := by
  simpa only [List.append_assoc, List.cons_append] using
    (List.perm_middle (a := x) (l₁ := xs ++ before) (l₂ := after))

/-- Shuffling the buckets in turn prepends a permutation of all of them. -/
theorem buckets {y0 y1 y2 y3 a b c k : List Term} (p0 : y0.Perm a) (p1 : y1.Perm b)
    (p2 : y2.Perm c) (p3 : y3.Perm k) :
    (y3 ++ (y2 ++ (y1 ++ y0))).Perm ([] ++ a ++ b ++ c ++ k) := by
  have reversed : (y3 ++ (y2 ++ (y1 ++ y0))).Perm (y0 ++ y1 ++ y2 ++ y3) :=
    List.perm_append_comm.trans (List.Perm.append (List.perm_append_comm.trans
      (List.Perm.append List.perm_append_comm (List.Perm.refl y2))) (List.Perm.refl y3))
  simpa only [List.nil_append] using
    reversed.trans (((p0.append p1).append p2).append p3)

end ShuffleProof
