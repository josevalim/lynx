module

public import Lynx
public import Erlang.sum

@[expose] public section

namespace Erlang.sum.laws

set_option maxHeartbeats 1000000 in
theorem «sum_empty/0» (schedule : List✝ Lynx.ScheduleChoice) :
    Lynx.run («sum_empty_ensures/0») schedule #[] 100 = Lynx.Outcome.ok Lynx.Term.true :=
  Lynx.law_of_pure
    (by clear schedule;
      exact by
        simp [«sum_empty_ensures/0», «sum/1», Erlang.lists.«sum/1», Erlang.lists.«sum/2»,
          Erlang.erlang.«==/2»])

theorem «sum_singleton/1» (x : Lynx.Term)
    (requires :
      ∃ schedule : List✝ Lynx.ScheduleChoice,
        Lynx.run («sum_singleton_requires/1» x) schedule #[] 100 = Lynx.Outcome.ok Lynx.Term.true)
    (schedule : List✝ Lynx.ScheduleChoice) :
    Lynx.run («sum_singleton_ensures/1» x) schedule #[] 100 = Lynx.Outcome.ok Lynx.Term.true :=
  Lynx.law_of_pure_requires («sum_singleton_requires/1_pure» x)
    (by clear requires schedule;
      exact fun requires => by
        cases x <;>
          simp [«sum_singleton_requires/1», «sum_singleton_ensures/1», Erlang.erlang.«is_integer/1»,
            «sum/1», Erlang.lists.«sum/1», Erlang.lists.«sum/2»,
            Erlang.erlang.«==/2»] at requires ⊢)
    requires

theorem «sum_empty_again/0» (schedule : List✝ Lynx.ScheduleChoice) :
    Lynx.run («sum_empty_ensures/0») schedule #[] 100 = Lynx.Outcome.ok Lynx.Term.true :=
  Lynx.law_of_pure
    (by clear schedule; exact by exact (Lynx.IsPure.run_eq_ok_iff (by simp)).mp («sum_empty/0» []))

end Erlang.sum.laws
