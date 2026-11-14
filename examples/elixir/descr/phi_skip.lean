
namespace Elixir.STTDescrProofsTest.FunSem
variable {V : Type}

/-- Skipping an arrow through argument `i`. -/
def skipAt (args : List (Bool × (V → Prop))) (i : Nat) (u : V → Prop) : List (Bool × (V → Prop)) :=
  args.set i (true, fun v => ((args[i]?.map Prod.snd).getD fun _ => False) v ∧ ¬u v)

theorem mem_skips : ∀ (us : List (V → Prop)) (args : List (Bool × (V → Prop))), us.length = args.length →
    ∀ a, a ∈ Skips us args ↔ ∃ i, ∃ h : i < us.length, a = skipAt args i us[i]
  | [], [], _, a => by simp [Skips]
  | u :: us, (b, x) :: as, len, a => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at len
    simp only [Skips, List.mem_cons, List.mem_map, mem_skips us as len]
    constructor
    · rintro (rfl | ⟨a', ⟨i, hi, rfl⟩, rfl⟩)
      · exact ⟨0, by simp, by simp [skipAt]⟩
      · exact ⟨i + 1, by simp; omega, by simp [skipAt]⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => left; simp [skipAt]
      | succ i =>
        have hi' : i < us.length := by simp at hi; omega
        right; exact ⟨skipAt as i us[i], ⟨i, hi', rfl⟩, by simp [skipAt]⟩
  | [], _ :: _, len, _ => by simp at len
  | _ :: _, [], len, _ => by simp at len

end Elixir.STTDescrProofsTest.FunSem

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

theorem any_congr_mem {α : Type} {f g : α → Bool} : ∀ (l : List α), (∀ p ∈ l, f p = g p) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a (by simp), any_congr_mem l fun p mp => h p (by simp [mp])]

theorem semA_set (args : List (Bool × Term)) (i : Nat) (p : Bool × Term) :
    semA den (args.set i p) = (semA den args).set i (p.1, den p.2) := by
  simp [semA, List.map_set]

/-- The answer of `phi/5` when no positive arrow is left. -/
theorem phi_base (ctx : PhiCtx E den K seen) {args : List (Bool × Term)} {ret : Bool × Term}
    (v : PhiOk E n args ret []) {cache : Term} (ok : CacheOk E den n cache) {m : Nat} (hm : K + 1 ≤ m) :
    ∃ b c, Elixir.Module.Types.Descr.«phi/5» (D m) (encA args) (encR ret) (encP []) cache seen =
        .ok (.tuple #[boolAtom b, c]) ∧
      (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den [])) ∧ CacheOk E den n c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨vA, vL, vR, -⟩ := v
  let res : Term → Bool := fun x => match x with
    | .tuple ⟨[.atom "true", a]⟩ => isEmpty den a
    | _ => Bool.false
  have hres : ∀ p ∈ args, res (.tuple #[boolAtom p.1, p.2]) = (p.1 && isEmpty den p.2) := by
    intro p _; cases p.1 <;> rfl
  have any := any_list (D (k + 1)) "Elixir.Module.Types.Descr" "-phi/5-fun-0-" #[seen] res
    (args.map fun p => .tuple #[boolAtom p.1, p.2]) (by
      intro x mx
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mx
      rw [Erlang.program.«Elixir.Module.Types.Descr:-phi/5-fun-0-/1».pure, hres p mp]
      have e := ctx.empty (vA p mp) k (by omega)
      cases hb : p.1 <;> simp [Elixir.Module.Types.Descr.«-phi/5-fun-0-/2», Lynx.Except.andAlso, boolAtom, e])
  have hany : (args.map fun p => Term.tuple #[boolAtom p.1, p.2]).any res =
      args.any (fun p => p.1 && isEmpty den p.2) := by
    rw [List.any_map]; exact any_congr_mem args fun p mp => hres p mp
  rw [hany] at any
  let r : Bool := args.any (fun p => p.1 && isEmpty den p.2) || (ret.1 && isEmpty den ret.2)
  have sem : r = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den []) := by
    simp only [r, semR, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, isEmpty_iff]
    constructor
    · rintro (⟨p, mp, hb, he⟩ | ⟨hb, he⟩)
      · exact Or.inl ⟨(p.1, den p.2), List.mem_map.mpr ⟨p, mp, rfl⟩, hb, he⟩
      · exact Or.inr ⟨hb, he⟩
    · rintro (⟨q, mq, hb, he⟩ | ⟨hb, he⟩)
      · obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mq
        exact Or.inl ⟨p, mp, hb, he⟩
      · exact Or.inr ⟨hb, he⟩
  obtain ⟨c, put, okc⟩ := cache_put ok ⟨vA, vL, vR, by simp⟩ sem
  refine ⟨r, c, ?_, sem, okc⟩
  have er := ctx.empty vR (k + 1) (by omega)
  have v11 : Lynx.Except.orElse (Erlang.lists.«any/2» (D (k + 1))
      (.function "Elixir.Module.Types.Descr" "-phi/5-fun-0-" 1 #[seen]) (encA args))
      (Lynx.Except.andAlso (pure (boolAtom ret.1)) (Elixir.Module.Types.Descr.«empty_seen?/2» (D (k + 1)) ret.2 seen)
        Bool.true) Bool.true = .ok (boolAtom r) := by
    simp only [encA]; rw [any, er]; simp only [r]
    cases h1 : ret.1 <;> cases h2 : args.any (fun p => p.1 && isEmpty den p.2) <;>
      cases h3 : isEmpty den ret.2 <;> simp [Lynx.Except.orElse, Lynx.Except.andAlso, boolAtom]
  rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
  simp only [encR, encP, List.map_nil, Term.list]
  simp only [pure_bind, v11, Lynx.Except.ok_bind]
  rw [show Term.tuple ⟨[boolAtom ret.1, ret.2]⟩ = encR ret from rfl, show Term.nil = encP [] from rfl, put]
  rfl

end

end Elixir.STTDescrProofsTest.Nest
