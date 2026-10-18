module

public import Lynx
public import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit

/-! Lemmas about exported definitions are proved when first used: by name, by
`simp`, or by the purity proofs of their callers. `LynxTest.Purity.LazyImport`
requests the remaining ones from another module. -/

@[expose] public section

namespace LynxTest.Purity.Lazy
open Lynx

#lynx_partial def lazyClassify (input : Term) : Result :=
  match input with
  | .integer _ => .ok (.atom "integer")
  | _ => .error (.error (.atom "badarg"))

#lynx_partial def lazyClassifyTwice (input : Term) : Result := do
  let _ ← lazyClassify input
  lazyClassify input

#lynx_partial def «lazyFind/2» (_0 : Term) (_1 : Term) : Result := do
  let _2 ← Result.ofExcept (Erlang.erlang.«</2» _0 _1)
  match _2 with
  | .atom "true" => pure _1
  | _ => do
    let _3 ← Result.ofExcept (Erlang.erlang.«+/2» _1 (.integer 4))
    «lazyFind/2» _0 _3
partial_fixpoint monotonicity by
  intro f g h
  repeat' first
    | exact Lean.Order.PartialOrder.rel_refl
    | exact h _ _
    | exact h _
    | apply Lynx.Result.bind_mono_pure
    | (intro)
    | split
    | simp_all

#lynx_partial def «lazyEach/1» (_0 : Term) : Result :=
  match _0 with
  | .cons head tail => do
    let _ ← «lazyFind/2» head (.integer 0)
    «lazyEach/1» tail
  | _ => pure .nil

#lynx_partial mutual
  def lazyRotateFirst (left right : Term) : Result :=
    match left with
    | .cons _ tail => lazyRotateThird tail right
    | _ => .ok right
  def lazyRotateSecond (left right : Term) : Result :=
    match right with
    | .cons _ tail => lazyRotateFirst left tail
    | _ => .ok left
  def lazyRotateThird (left right : Term) : Result :=
    match left with
    | .cons _ tail => lazyRotateSecond tail right
    | _ => .ok right
end

-- Structural recursion over tuple fields, like gb_trees node counts.
#lynx_partial def lazyNodes (_0 : Term) : Result :=
  match _0 with
  | .atom "nil" => pure (.integer 0)
  | .tuple ⟨[_, left, right]⟩ => do
    let a ← lazyNodes left
    let b ← lazyNodes right
    Result.ofExcept (Erlang.erlang.«+/2» a b)
  | _ => .error (.error (.atom "function_clause"))

-- Well-founded recursion, where a call passes its parameter unchanged.
#lynx_partial mutual
  def lazyCheck : Term → Term → Result
    | .cons x xs, depth => lazyItems (.cons x xs) depth
    | _, _ => .ok (.atom "true")
  termination_by data _ => (sizeOf data, 1)
  def lazyItems : Term → Term → Result
    | .cons x xs, depth => do
      let _ ← lazyCheck x depth
      lazyItems xs depth
    | _, _ => .ok (.atom "true")
  termination_by data _ => (sizeOf data, 0)
end

-- Nothing is proved until a lemma is requested.
run_meta do
  for name in [`lazyClassify_partial, `lazyClassifyTwice_partial, `lazyRotateFirst_partial] do
    if (← Lean.getEnv).contains (`LynxTest.Purity.Lazy ++ name) then
      throwError "{name} was proved eagerly"

-- Callers realize the lemmas of their callees.
example (input : Term) : Result.IsPartial (lazyClassifyTwice input) := by simp
example (input : Term) : Result.IsPartial (lazyClassify input) := lazyClassify_partial input
example (a b : Term) : Result.IsPartial («lazyFind/2» a b) := «lazyFind/2_partial» a b
example (left right : Term) : Result.IsPartial (lazyRotateSecond left right) := by simp

example (t : Term) : Result.IsPartial (lazyNodes t) := lazyNodes_partial t

-- `simp_all` may visit partiality predicates that are not fully applied.
example (root output : Term) (returned : lazyNodes root = .ok output) : True := by
  have partialCases (computation : Result) (partiality : computation.IsPartial) :
      computation = .exhausted ∨ (∃ value, computation = .ok value) ∨
        (∃ exception, computation = .error exception) := by
    cases computation <;> simp_all [Result.IsPartial]
  induction root using lazyNodes.induct generalizing output with
  | case1 => trivial
  | case2 => trivial
  | case3 => simp_all [lazyNodes]

-- An impure definition fails when its lemma is requested.
#lynx_partial def lazyReads : Result := .get fun _ => .ok .nil

#guard_msgs (drop error) in
example : Result.IsPartial lazyReads := lazyReads_partial

end LynxTest.Purity.Lazy

end

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Purity.Lazy
