namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

/-- Positive arrows of arity `n` with element types. -/
def PosOk (E : Term → Prop) (n : Nat) (P : List (Term × List Term × Term)) : Prop :=
  ∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2 ∧ p.2.1.length = n

theorem semP_len {P : List (Term × List Term × Term)} (hP : PosOk E n P) {args : List (Bool × Term)}
    (len : args.length = n) : ∀ p ∈ semP den P, p.1.length = (semA den args).length := by
  intro p mp
  obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
  simp [semA, (hP q mq).2.2, len]

theorem phiArgs_nil (d : Dispatcher) (j args ret P cache seen : Term) :
    Elixir.Module.Types.Descr.«phi_arguments/7» d .nil j args ret P cache seen = .ok (.tuple #[.atom "true", cache]) := by
  rw [Elixir.Module.Types.Descr.«phi_arguments/7».eq_def]; rfl

/-- `phi_arguments/7` checks the skips of an arrow through its remaining arguments, given that `phi/5` answers
for the remaining arrows. -/
theorem phiArgs_run (ctx : PhiCtx E den K seen) {m : Nat} (hm : K ≤ m) {args : List (Bool × Term)}
    (hA : ∀ p ∈ args, E p.2) (lA : args.length = n) {ret : Bool × Term} (hR : E ret.2)
    {P : List (Term × List Term × Term)} (hP : PosOk E n P)
    (ih : ∀ args' cache, (∀ p ∈ args', E p.2) → args'.length = n → CacheOk E den n cache →
      ∃ b c, Elixir.Module.Types.Descr.«phi/5» (D m) (encA args') (encR ret) (encP P) cache seen =
          .ok (.tuple #[boolAtom b, c]) ∧
        (b = Bool.true ↔ FunSem.phiS (semA den args') (semR den ret) (semP den P)) ∧ CacheOk E den n c) :
    ∀ (suf : List Term) (j : Nat), j + suf.length = n → (∀ u ∈ suf, E u) → ∀ cache, CacheOk E den n cache →
      ∃ b c, Elixir.Module.Types.Descr.«phi_arguments/7» (D m) (Term.list suf) (.integer j) (encA args) (encR ret)
          (encP P) cache seen = .ok (.tuple #[boolAtom b, c]) ∧
        (b = Bool.true ↔ ∀ i (h : i < suf.length),
          FunSem.phiS (FunSem.skipAt (semA den args) (j + i) (den suf[i])) (semR den ret) (semP den P)) ∧
        CacheOk E den n c
  | [], j, _, _, cache, ok => ⟨Bool.true, cache, by simpa [Term.list, boolAtom] using phiArgs_nil _ _ _ _ _ cache seen,
      by simp, ok⟩
  | u :: suf, j, hj, hu, cache, ok => by
    have jn : j < args.length := by simp at hj; omega
    have hu₀ : E u := hu u (by simp)
    obtain ⟨c, hc, rc, sc⟩ := ctx.diff (hA _ (List.getElem_mem jn)) hu₀
    have ec := ctx.empty hc m hm
    -- The first skip.
    have first : ∃ b₁ c₁, (do
          let x ← Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c seen
          Lynx.Except.guard (.ok (x.isMember [.atom "false", .atom "nil"]))
            (fun _ => do
              let a ← Elixir.List.«replace_at/3» (encA args) (.integer j) (.tuple #[.atom "true", c])
              Elixir.Module.Types.Descr.«phi/5» (D m) a (encR ret) (encP P) cache seen)
            fun _ => pure (.tuple #[.atom "true", cache])) = .ok (.tuple #[boolAtom b₁, c₁]) ∧
        (b₁ = Bool.true ↔ FunSem.phiS (FunSem.skipAt (semA den args) j (den u)) (semR den ret) (semP den P)) ∧
        CacheOk E den n c₁ := by
      have skip : FunSem.skipAt (semA den args) j (den u) = semA den (args.set j (Bool.true, c)) := by
        rw [semA_set]
        simp only [FunSem.skipAt]
        congr 2
        funext v
        simp only [semA, List.getElem?_map, jn, List.getElem?_eq_getElem, Option.map_some, Option.getD_some]
        exact propext (sc v).symm
      rw [ec]
      cases he : isEmpty den c
      · have rep := replace_list (args.map fun p => Term.tuple #[boolAtom p.1, p.2]) j (.tuple #[boolAtom Bool.true, c])
          (by simp [jn])
        replace rep : Elixir.List.«replace_at/3» (encA args) (.integer j) (.tuple #[boolAtom Bool.true, c]) =
            .ok (encA (args.set j (Bool.true, c))) := by
          rw [← encA_set]; exact rep
        obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := ih (args.set j (Bool.true, c)) cache
          (fun p mp => by
            rcases List.mem_or_eq_of_mem_set mp with mp | rfl
            · exact hA p mp
            · exact hc)
          (by simp [lA]) ok
        refine ⟨b₁, c₁, ?_, by rw [skip]; exact s₁, o₁⟩
        simp only [guard_member, Bool.false_eq_true, ite_false, Lynx.Except.ok_bind]
        rw [show Term.tuple #[.atom "true", c] = .tuple #[boolAtom Bool.true, c] from rfl, rep, Lynx.Except.ok_bind]
        exact r₁
      · refine ⟨Bool.true, cache, by simp [boolAtom], ?_, ok⟩
        simp only [true_iff]
        rw [skip, semA_set]
        exact FunSem.phiS_empty_arg _ j (by simp [semA, jn]) (den c) _ _ (semP_len hP lA) ((isEmpty_iff den c).mp he)
    obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := first
    obtain ⟨b₂, c₂, r₂, s₂, o₂⟩ := phiArgs_run ctx hm hA lA hR hP ih suf (j + 1) (by simp at hj; omega)
      (fun u' mu => hu u' (by simp [mu])) c₁ o₁
    have nth := nth_list (args.map fun p => Term.tuple #[boolAtom p.1, p.2]) j (by simp [jn])
    simp only [List.getElem_map] at nth
    refine ⟨b₁ && b₂, if b₁ then c₂ else c₁, ?_, ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«phi_arguments/7».eq_def]
      simp only [Erlang.erlang.«+/2_integers»]
      simp only [encA] at nth r₁ r₂ ⊢
      rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega] at r₂
      simp only [Lynx.Except.ok_bind]
      rw [nth]
      simp only [rc m hm, Lynx.Except.ok_bind]
      rw [r₁]
      cases b₁ <;> simp [r₂]
    · rw [Bool.and_eq_true, s₁, s₂]
      constructor
      · rintro ⟨h₀, hs⟩ i hi
        cases i with
        | zero => simpa using h₀
        | succ i =>
          have := hs i (by simp at hi; omega)
          rw [show j + 1 + i = j + (i + 1) by omega] at this
          simpa using this
      · intro h
        refine ⟨h 0 (by simp), fun i hi => ?_⟩
        have := h (i + 1) (by simp; omega)
        rw [show j + (i + 1) = j + 1 + i by omega] at this
        simpa using this
    · cases b₁ <;> simp [o₁, o₂]

end

end Elixir.STTDescrProofsTest.Nest
