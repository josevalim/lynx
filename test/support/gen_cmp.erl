-module(gen_cmp).
-export([main/1]).
main([Output]) ->
  Terms = [-123456789012345678901234567890, -1, 0, 1, 123456789012345678901234567890,
           -0.0, 0.0, 1.0, -2.5, a, z, {}, {a,1}, #{}, #{1 => a}, [], [a], [a|b], <<>>, <<1>>, <<1:1>>],
  Max = 1.7976931348623157e308,
  MinNormal = 2.2250738585072014e-308,
  <<MinBits:64/unsigned>> = <<MinNormal:64/float>>,
  <<Before:64/float>> = <<(MinBits - 1):64/unsigned>>,
  <<After:64/float>> = <<(MinBits + 1):64/unsigned>>,
  Edge = [-0.0, 0.0, 0, 1, 1.0, 9007199254740992, 9007199254740993,
          9007199254740992.0, 1 bsl 1100, -(1 bsl 1100), Max,
          5.0e-324, -5.0e-324, Before, MinNormal, After,
          1.0000000000000002, 0.1 + 0.2, 0.3,
          {1}, {1.0}, [1], [1.0], #{1 => a}, #{1.0 => a}, #{1 => a, 1.0 => b}],
  Pairs = [{A,B,erts_internal:cmp_term(A,B)} || A <- Terms, B <- Terms] ++
          [{A,B,erts_internal:cmp_term(A,B)} || A <- Edge, B <- Edge],
  Indexed = lists:zip(lists:seq(1,length(Pairs)),Pairs),
  Exports = [io_lib:format("c~p/0",[I]) || {I,_} <- Indexed],
  Laws = [io_lib:format("-law #{name => {l~p, []}, ensures => c~p}.~n-proof ~~\"\"\"~n~ts~n\"\"\".~n",[I,I,proof(I, A, B, R)]) || {I,{A,B,R}} <- Indexed],
  Funs = [io_lib:format("c~p() -> erts_internal:cmp_term(~p, ~p) =:= ~p.~n",[I,A,B,R]) || {I,{A,B,R}} <- Indexed],
  ok = file:write_file(Output, unicode:characters_to_binary(["-module(cmp_literal_diff).\n-export([",lists:join(",",Exports),"]).\n",Laws,Funs])),
  io:format("~p base terms, ~p edge terms, ~p pairs; cmp(1,1.0)=~p~n", [length(Terms),length(Edge),length(Pairs),erts_internal:cmp_term(1,1.0)]).

proof(I, A, B, R) when is_float(A), is_float(B) ->
  <<SA:1, EA:11, FA:52>> = <<A:64/float>>,
  <<SB:1, EB:11, FB:52>> = <<B:64/float>>,
  TA = io_lib:format("(.float ⟨~s, ~p, ~p⟩)",[bool(SA),EA,FA]),
  TB = io_lib:format("(.float ⟨~s, ~p, ~p⟩)",[bool(SB),EB,FB]),
  Ord = case R of -1 -> "lt"; 0 -> "eq"; 1 -> "gt" end,
  io_lib:format("have h : Lynx.Term.compareExact (Lynx.Term.fuel ~ts ~ts) ~ts ~ts = .~s := by~n  rw [Lynx.Term.compareExact_step]~n  simp only [Lynx.Term.Compare.compareStep, Lynx.Term.Compare.exactFloatCompare, Lynx.Term.Compare.exactFloatCompareSlow, compareLex, Lynx.Term.Compare.compareOn, Lynx.Term.Compare.ratCompare_finiteFloat, Lynx.Term.FiniteFloat.signedScaled, Lynx.Term.FiniteFloat.scaled, compareOfLessAndEq]~n  all_goals decide~nsimp [«c~p/0», Erlang.erts_internal.«cmp_term/2», h, Erlang.erlang.«=:=/2»]",[TA,TB,TA,TB,Ord,I]);
proof(_, _, _, _) -> "rfl".
bool(0) -> "false";
bool(1) -> "true".
