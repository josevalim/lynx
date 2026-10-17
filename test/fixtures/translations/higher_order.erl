-module(higher_order).
-export([map/2, proper_list/1, map_returns_list_requires/2, map_returns_list_ensures/2]).

%% Laws cannot quantify over arbitrary functions: a function parameter is
%% restricted to the listed functions, which the proof resolves through the
%% program's function table.
-law #{name => {map_returns_list, [list, callback]},
       requires => map_returns_list_requires, ensures => map_returns_list_ensures}.
-proof ~"""
rw [Lynx.IsPure.run_eq_ok_iff (by simp)] at requires
have valid : «proper_list/1» list = .ok Lynx.Term.true ∧
    (callback = .function 0 1 #[] ∨ callback = .function 1 1 #[]) := by
  cases proper : «proper_list/1» list <;>
    simp [«map_returns_list_requires/2», proper] at requires
  split at requires <;> simp_all [Erlang.lists.«member/2»]
  by_cases first : callback = .function 0 1 #[] <;> simp_all
-- Each listed function resolves through the table without consuming depth.
have maps : ∀ input, «proper_list/1» input = .ok Lynx.Term.true →
    ∃ out, Lynx.Result.resolve Erlang.program.fun_table 100 («map/2» input callback) = .ok out ∧
      Erlang.erlang.«is_list/1» out = .ok Lynx.Term.true := by
  intro input proper
  induction input using «proper_list/1».induct with
  | case1 => exact ⟨.nil, by simp [«map/2»], rfl⟩
  | case2 head tail ih =>
    obtain ⟨out, resolved, _⟩ := ih (by simpa [«proper_list/1»] using proper)
    rcases valid.2 with rfl | rfl
    · exact ⟨.cons head out, by simp [«map/2», Lynx.Result.resolve_bind, resolved,
        «$lynx_fun_0/1»], rfl⟩
    · exact ⟨.cons (.tuple #[head]) out, by simp [«map/2», Lynx.Result.resolve_bind, resolved,
        «$lynx_fun_1/1»], rfl⟩
  | case3 => simp_all [«proper_list/1»]
obtain ⟨out, resolved, list⟩ := maps list valid.1
exact Lynx.run_of_resolve rfl
  (by simp [«map_returns_list_ensures/2», Lynx.Result.resolve_bind, resolved, list])
""".

map([], _F) -> [];
map([Head | Tail], F) -> [F(Head) | map(Tail, F)].

proper_list([]) -> true;
proper_list([_ | Tail]) -> proper_list(Tail);
proper_list(_) -> false.

map_returns_list_requires(List, F) ->
    proper_list(List) andalso lists:member(F, [fun(X) -> X end, fun(X) -> {X} end]).

map_returns_list_ensures(List, F) -> is_list(map(List, F)).
