namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The cache of `phi/5` and the context it runs in. -/

section
variable {V : Type} (E : Term → Prop) (den : Term → V → Prop)

/-- Whether a set is empty, as a Boolean. -/
noncomputable def isEmpty (a : Term) : Bool := @decide (∀ v, ¬den a v) (Classical.propDecidable _)

theorem isEmpty_iff (a : Term) : isEmpty den a = Bool.true ↔ ∀ v, ¬den a v := by
  simp [isEmpty]

/-- Element types, closed under the operations `phi/5` performs, whose emptiness is decided under `seen`,
from call depth `K`. -/
structure PhiCtx (K : Nat) (seen : Term) : Prop where
  inter : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∧ den b v
  diff : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∧ ¬den b v
  empty : ∀ {a}, E a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a seen = .ok (boolAtom (isEmpty den a))
  congr : DenCongr E den

/-- Arguments, return, and positive arrows of arity `n`, of element types. -/
def PhiOk (n : Nat) (args : List (Bool × Term)) (ret : Bool × Term) (P : List (Term × List Term × Term)) : Prop :=
  (∀ p ∈ args, E p.2) ∧ args.length = n ∧ E ret.2 ∧ ∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2 ∧ p.2.1.length = n

/-- Cached answers of `phi/5` are its answers. -/
def CacheOk (n : Nat) (cache : Term) : Prop :=
  ∃ M, cache = .map M ∧ ∀ e ∈ M, ∃ args ret P b, PhiOk E n args ret P ∧
    e.1 = .tuple #[encA args, encR ret, encP P] ∧ e.2 = boolAtom b ∧
    (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P))

theorem cacheOk_nil (n : Nat) : CacheOk E den n (.map []) := ⟨[], rfl, by simp⟩

end

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n : Nat}

theorem semR_cmp (cg : DenCongr E den) {r r' : Bool × Term} (h : E r.2) (h' : E r'.2)
    (e : Term.compare (Term.fuel (encR r) (encR r')) (encR r) (encR r') = .eq) : semR den r = semR den r' := by
  obtain ⟨eb, ea⟩ := tuple2_cmp e
  simp only [semR, boolAtom_cmp eb, cg h h' ea]

/-- Storing an answer keeps the cache correct. -/
theorem cache_put {cache : Term} (ok : CacheOk E den n cache) {args : List (Bool × Term)} {ret : Bool × Term}
    {P : List (Term × List Term × Term)} (v : PhiOk E n args ret P) {b : Bool}
    (sem : b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P)) :
    ∃ c, Erlang.maps.«put/3» (.tuple #[encA args, encR ret, encP P]) (boolAtom b) cache = .ok c ∧ CacheOk E den n c := by
  obtain ⟨M, rfl, hM⟩ := ok
  refine ⟨_, rfl, _, rfl, fun e me => ?_⟩
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨args, ret, P, b, v, rfl, rfl, sem⟩
  · exact hM e me

/-- A cached answer is the answer. -/
theorem cache_get (cg : DenCongr E den) {cache : Term} (ok : CacheOk E den n cache) {args : List (Bool × Term)}
    {ret : Bool × Term} {P : List (Term × List Term × Term)} (v : PhiOk E n args ret P) {w : Term}
    (h : getMapKeys [.tuple #[encA args, encR ret, encP P]] cache = [w]) :
    ∃ b, w = boolAtom b ∧ (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P)) := by
  obtain ⟨M, rfl, hM⟩ := ok
  rw [getMapKeys_single] at h
  cases hl : mapLookup M (.tuple #[encA args, encR ret, encP P]) with
  | none => rw [hl] at h; cases h
  | some w' =>
    rw [hl] at h; simp at h; subst h
    simp only [mapLookup, Option.map_eq_some_iff] at hl
    obtain ⟨e, he, rfl⟩ := hl
    have me := List.mem_of_find?_eq_some he
    have qe : compareExact (fuel (.tuple #[encA args, encR ret, encP P]) e.1) (.tuple #[encA args, encR ret, encP P]) e.1 = .eq := by simpa using List.find?_some he
    obtain ⟨args', ret', P', b, v', e1, e2, sem⟩ := hM e me
    rw [e1] at qe
    have ce := compare_eq_of_compareExact_eq _ _ qe
    obtain ⟨b₀, b₁, b₂, eq, c₀, c₁, c₂⟩ := tuple3_cmp ce
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eq
    obtain ⟨rfl, rfl, rfl, -⟩ := eq
    refine ⟨b, e2, ?_⟩
    rw [semA_cmp cg v.1 v'.1 c₀, semR_cmp cg v.2.2.1 v'.2.2.1 c₁,
      semP_cmp cg (fun p mp => ⟨(v.2.2.2 p mp).1, (v.2.2.2 p mp).2.1⟩)
        (fun p mp => ⟨(v'.2.2.2 p mp).1, (v'.2.2.2 p mp).2.1⟩) c₂]
    exact sem

end

end Elixir.STTDescrProofsTest.Nest
