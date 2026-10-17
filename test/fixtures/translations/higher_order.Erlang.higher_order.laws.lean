module

public import Lynx
public import Erlang.higher_order
public import Erlang.program

@[expose] public section

namespace Erlang.higher_order.laws

theorem «map_returns_list/2» (list : Lynx.Term) (callback : Lynx.Term)
    (requires :
      ∃ schedule : List✝ Lynx.ScheduleChoice,
        Lynx.run («map_returns_list_requires/2» list callback) schedule Erlang.program.fun_table
            100 =
          Lynx.Outcome.ok Lynx.Term.true)
    (schedule : List✝ Lynx.ScheduleChoice) :
    Lynx.run («map_returns_list_ensures/2» list callback) schedule Erlang.program.fun_table 100 =
      Lynx.Outcome.ok Lynx.Term.true :=
  by
  obtain ⟨_, requires⟩ := requires
  rw [Lynx.IsPure.run_eq_ok_iff (by simp)] at requires
  have valid :
    «proper_list/1» list = .ok Lynx.Term.true ∧
      (callback = .function 0 1 #[] ∨ callback = .function 1 1 #[]) :=
    by
    cases proper : «proper_list/1» list <;> simp [«map_returns_list_requires/2», proper] at requires
    split at requires <;> simp_all [Erlang.lists.«member/2»]
    by_cases first : callback = .function 0 1 #[] <;> simp_all
  have maps :
    ∀ input,
      «proper_list/1» input = .ok Lynx.Term.true →
        ∃ out,
          Lynx.Result.resolve Erlang.program.fun_table 100 («map/2» input callback) = .ok out ∧
            Erlang.erlang.«is_list/1» out = .ok Lynx.Term.true :=
    by
    intro input proper
    induction input using «proper_list/1».induct with
    | case1 => exact ⟨.nil, by simp [«map/2»], rfl⟩
    | case2 head tail
      ih =>
      obtain ⟨out, resolved, _⟩ := ih (by simpa [«proper_list/1»] using proper)
      rcases valid.2 with rfl | rfl
      ·
        exact
          ⟨.cons head out, by simp [«map/2», Lynx.Result.resolve_bind, resolved, «$lynx_fun_0/1»],
            rfl⟩
      ·
        exact
          ⟨.cons (.tuple #[head]) out, by
            simp [«map/2», Lynx.Result.resolve_bind, resolved, «$lynx_fun_1/1»], rfl⟩
    | case3 => simp_all [«proper_list/1»]
  obtain ⟨out, resolved, list⟩ := maps list valid.1
  exact
    Lynx.run_of_resolve rfl
      (by simp [«map_returns_list_ensures/2», Lynx.Result.resolve_bind, resolved, list]) _

end Erlang.higher_order.laws
