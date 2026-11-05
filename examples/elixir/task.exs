# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/task.exs
#
# Task.async/1 and Task.await/2 compute in a linked process and reply through
# a monitor alias. Awaiting without a timeout returns the task's result under
# every schedule. The input is an arbitrary integer, but the processes take the
# same steps for every value, so the proof evaluates every interleaving.
ExUnit.start()

defmodule TaskProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def double_in_task(x) do
    task = Task.async(fn -> x * 2 end)
    Task.await(task, :infinity)
  end

  laws "Task" do
    # Task.Supervised runs the task with apply(:erlang, :apply, [fun, []]).
    dynamic &:erlang.apply/2

    # The task does not raise, so its crash report is unreachable.
    cutoff &Task.Supervised.get_running/1
    cutoff &Task.Supervised.format_report/1
    cutoff &:proc_lib.get_label/1
    cutoff &:logger.error/2

    # The owner awaits its own task, so it never reports another owner.
    cutoff &Task.invalid_owner_error/1
    cutoff &ArgumentError.exception/1

    law double_in_task_doubles(x),
      requires: is_integer(x),
      expects: double_in_task(x) == x * 2,
      proof: ~LEAN"""
      obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
        cases x <;> simp_all [«double_in_task_doubles:requires/1», Erlang.erlang.«is_integer/1»]
      -- Evaluate every interleaving; only the final comparison depends on n.
      have checked := Lynx.concurrent_of_check
        (Lynx.apply «double_in_task_doubles:ensures/1» Erlang.program.fun_table (.integer n))
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 300
        (by cbv; simp [Rat.lt_irrefl]) schedule
      split at checked
      · assumption
      · contradiction
      """
  end
end
