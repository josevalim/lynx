module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.higher_order
public import Erlang.program
meta import Erlang.higher_order
meta import Erlang.program

@[expose] public section

namespace Erlang.higher_order.laws

theorem «map_returns_list/2» (list : Lynx.Term) (callback : Lynx.Term)
    (requires : «map_returns_list_requires/2» list callback = Except.ok Lynx.Term.true) :
    ∃ bound : Nat,
      ∀ depth : Nat,
        bound ≤ depth →
          Lynx.apply «map_returns_list_ensures/2» Erlang.program.fun_table depth list callback =
            Except.ok Lynx.Term.true := by
  have valid : «proper_list/1» list = .ok Lynx.Term.true ∧
      (callback = .function "higher_order" "-map_returns_list_requires/2-fun-0-" 1 #[] ∨ callback = .function "higher_order" "-map_returns_list_requires/2-fun-1-" 1 #[]) := by
    cases proper : «proper_list/1» list <;>
      simp [«map_returns_list_requires/2», proper, Lynx.Except.andAlso_eq] at requires
    split at requires <;> simp_all [Erlang.lists.«member/2»]
    by_cases first : callback = .function "higher_order" "-map_returns_list_requires/2-fun-0-" 1 #[] <;> simp_all
  -- Each listed function is pure, so calling it consumes no depth, and any depth works.
  refine ⟨0, fun depth _ => ?_⟩
  have maps : ∀ input, «proper_list/1» input = .ok Lynx.Term.true →
      ∃ out, «map/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table depth) input callback = .ok out ∧
        Erlang.erlang.«is_list/1» out = .ok Lynx.Term.true := by
    intro input proper
    induction input using «proper_list/1».induct with
    | case1 => exact ⟨.nil, by simp [«map/2»], rfl⟩
    | case2 head tail ih =>
      obtain ⟨out, returned, _⟩ := ih (by simpa [«proper_list/1»] using proper)
      rcases valid.2 with rfl | rfl
      · exact ⟨.cons (.tuple #[head]) out, by simp [«map/2», returned, «-map_returns_list_requires/2-fun-0-/1»], rfl⟩
      · exact ⟨.cons head out, by simp [«map/2», returned, «-map_returns_list_requires/2-fun-1-/1»], rfl⟩
    | case3 => simp_all [«proper_list/1»]
  obtain ⟨out, returned, list⟩ := maps list valid.1
  simp [«map_returns_list_ensures/2», returned, list]

end Erlang.higher_order.laws
