namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

/-- `phi/5` answers whether no row with its arguments and result is allowed by all its arrows. -/
theorem phi_run (ctx : PhiCtx E den K seen) {m : Nat} (hm : K + 1 ≤ m) :
    ∀ (P : List (Term × List Term × Term)), PosOk E n P → ∀ (args : List (Bool × Term)) (ret : Bool × Term) cache,
      (∀ p ∈ args, E p.2) → args.length = n → E ret.2 → CacheOk E den n cache →
      ∃ b c, Elixir.Module.Types.Descr.«phi/5» (D m) (encA args) (encR ret) (encP P) cache seen =
          .ok (.tuple #[boolAtom b, c]) ∧
        (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P)) ∧ CacheOk E den n c
  | [], _, args, ret, cache, hA, lA, hR, ok => phi_base ctx ⟨hA, lA, hR, by simp⟩ ok hm
  | (key, us, s) :: P, hP, args, ret, cache, hA, lA, hR, ok => by
    have hP' : PosOk E n P := fun p mp => hP p (by simp [mp])
    obtain ⟨hU, hS, lU⟩ := hP (key, us, s) (by simp)
    have valid : PhiOk E n args ret ((key, us, s) :: P) := ⟨hA, lA, hR, hP⟩
    have ih := phi_run ctx hm P hP'
    have ok2 := ok
    obtain ⟨M, eM, hM⟩ := ok2
    subst eM
    -- What the arrow means.
    have unfoldS : FunSem.phiS (semA den args) (semR den ret) (semP den ((key, us, s) :: P)) ↔
        FunSem.phiS (semA den args) (Bool.true, fun v => den ret.2 v ∧ den s v) (semP den P) ∧
          ∀ i (h : i < us.length), FunSem.phiS (FunSem.skipAt (semA den args) (0 + i) (den us[i])) (semR den ret)
            (semP den P) := by
      simp only [semP, List.map_cons, FunSem.phiS, semR]
      refine and_congr_right fun _ => ?_
      rw [show (P.map fun p => (p.2.1.map den, den p.2.2)) = semP den P from rfl]
      constructor
      · intro h i hi
        exact h _ ((FunSem.mem_skips _ _ (by simp [semA, lU, lA]) _).mpr ⟨i, by simpa using hi, by simp⟩)
      · intro h a ma
        obtain ⟨i, hi, rfl⟩ := (FunSem.mem_skips _ _ (by simp [semA, lU, lA]) _).mp ma
        simpa using h i (by simpa using hi)
    have key_eq : Term.tuple #[encA args, encR ret, encP ((key, us, s) :: P)] =
        .tuple #[encA args, .tuple #[boolAtom ret.1, ret.2], .cons (.tuple #[key, Term.list us, s]) (encP P)] := rfl
    cases hl : mapLookup M (.tuple #[encA args, encR ret, encP ((key, us, s) :: P)]) with
    | some w =>
      obtain ⟨b, rfl, sem⟩ := cache_get ctx.congr ⟨M, rfl, hM⟩ valid (w := w) (by rw [getMapKeys_single, hl]; rfl)
      refine ⟨b, .map M, ?_, sem, ⟨M, rfl, hM⟩⟩
      rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
      rw [key_eq] at hl
      simp only [encR, encP, List.map_cons, Term.list] at hl ⊢
      simp [getMapKeys_single, hl]
    | none =>
      obtain ⟨c, hc, rc, sc⟩ := ctx.inter hR hS
      have ec := ctx.empty hc m (by omega)
      have denc : den c = fun v => den ret.2 v ∧ den s v := funext fun v => propext (sc v)
      -- The arrow used: the return meets the arrow's return.
      have first : ∃ b₁ c₁, (do
            let x ← Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c seen
            Lynx.Except.guard (.ok (x.isMember [.atom "false", .atom "nil"]))
              (fun _ => Elixir.Module.Types.Descr.«phi/5» (D m) (encA args) (.tuple #[.atom "true", c]) (encP P)
                (.map M) seen)
              fun _ => pure (.tuple #[.atom "true", .map M])) = .ok (.tuple #[boolAtom b₁, c₁]) ∧
          (b₁ = Bool.true ↔ FunSem.phiS (semA den args) (Bool.true, fun v => den ret.2 v ∧ den s v) (semP den P)) ∧
          CacheOk E den n c₁ := by
        rw [ec]
        cases he : isEmpty den c
        · obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := ih args (Bool.true, c) (.map M) hA lA hc ok
          refine ⟨b₁, c₁, ?_, ?_, o₁⟩
          · simp only [Lynx.Except.ok_bind, guard_member, Bool.false_eq_true, ite_false]; exact r₁
          · rw [s₁]; simp [semR, denc]
        · refine ⟨Bool.true, .map M, by simp [boolAtom], ?_, ok⟩
          simp only [true_iff]
          exact FunSem.phiS_empty_ret _ _ _ (semP_len hP' lA) fun v hv =>
            (isEmpty_iff den c).mp he v ((sc v).mpr hv)
      obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := first
      have miss : getMapKeys [.tuple #[encA args, encR ret, encP ((key, us, s) :: P)]] (.map M) = [] := by
        rw [getMapKeys_single, hl]; rfl
      rw [key_eq] at miss
      cases b₁
      · -- The arrow used is not covered: the answer is false.
        obtain ⟨c', put, o'⟩ := cache_put o₁ valid (b := Bool.false)
          (by simp only [Bool.false_eq_true, false_iff, unfoldS, not_and]; intro h; exact absurd h (by simpa using s₁))
        refine ⟨Bool.false, c', ?_, ?_, o'⟩
        · rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
          rw [key_eq] at put
          simp only [encR, encP, List.map_cons, Term.list] at miss put ⊢
          simp only [pure_bind, miss]
          simp only [encP] at r₁
          rw [rc m (by omega), Lynx.Except.ok_bind, r₁, Lynx.Except.ok_bind]
          simp only [boolAtom_false]
          rw [show Term.atom "false" = boolAtom Bool.false from rfl, put]
          rfl
        · simp only [Bool.false_eq_true, false_iff, unfoldS, not_and]; intro h; exact absurd h (by simpa using s₁)
      · obtain ⟨b₂, c₂, r₂, s₂, o₂⟩ := phiArgs_run ctx (by omega) hA lA hR hP'
          (fun args' cache h l o => ih args' ret cache h l hR o) us 0 (by simp [lU]) hU c₁ o₁
        have sem : b₂ = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den ((key, us, s) :: P)) := by
          rw [unfoldS, s₂]; simp only [s₁.mp rfl, true_and]
        obtain ⟨c', put, o'⟩ := cache_put o₂ valid sem
        refine ⟨b₂, c', ?_, sem, o'⟩
        rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
        rw [key_eq] at put
        simp only [encR, encP, List.map_cons, Term.list] at miss put ⊢
        simp only [pure_bind, miss]
        simp only [encP] at r₁ r₂
        rw [rc m (by omega), Lynx.Except.ok_bind, r₁, Lynx.Except.ok_bind]
        simp only [boolAtom_true]
        rw [show ((0 : Nat) : Int) = 0 from rfl] at r₂
        rw [show Term.tuple ⟨[boolAtom ret.1, ret.2]⟩ = encR ret from rfl, r₂, Lynx.Except.ok_bind]
        dsimp only
        rw [show encR ret = Term.tuple #[boolAtom ret.1, ret.2] from rfl, put]
        rfl

end

end Elixir.STTDescrProofsTest.Nest
