# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/task.exs
#
# Task.async/1 and Task.await/2 compute in a linked process and reply through
# a monitor alias. Awaiting without a timeout returns the task's result under
# every schedule, and awaiting with one either returns it or times out. The
# input is an arbitrary integer, but the processes take the same steps for
# every value, so the proofs evaluate every interleaving. Ignoring a task
# leaves its reply out of the owner's inbox.
ExUnit.start()

defmodule TaskProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def double_in_task(x) do
    task = Task.async(fn -> x * 2 end)
    Task.await(task, :infinity)
  end

  def double_or_timeout(x) do
    task = Task.async(fn -> x * 2 end)

    try do
      Task.await(task, 100)
    catch
      :exit, {:timeout, _} -> :timeout
    end
  end

  def ignore_leaves_no_reply do
    task = Task.async(fn -> :reply end)
    result = Task.ignore(task)

    # Once the task exits, no other process can send to the owner.
    monitor = Process.monitor(task.pid)

    receive do
      {:DOWN, ^monitor, _, _, _} -> :ok
    end

    empty? =
      receive do
        _ -> false
      after
        0 -> true
      end

    result in [{:ok, :reply}, nil] and empty?
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

    # Tasks are maps, so task.pid never reports a non-map.
    cutoff &:elixir_erl_pass.no_parens_remote/2

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

    law double_or_timeout_doubles(x),
      requires: is_integer(x),
      expects: double_or_timeout(x) in [x * 2, :timeout],
      proof: ~LEAN"""
      obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
        cases x <;> simp_all [«double_or_timeout_doubles:requires/1», Erlang.erlang.«is_integer/1»]
      -- The timeout may expire before or after the reply arrives. When the
      -- reply wins, the owner compares n * 2 with itself while the task is
      -- still running, so evaluation resumes after simp decides it.
      have checked := Lynx.concurrent_of_check
        (Lynx.apply «double_or_timeout_doubles:ensures/1» Erlang.program.fun_table (.integer n))
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 300
        (by cbv; repeat (simp only [Int.lt_irrefl, ite_false, ite_true]; cbv)) schedule
      split at checked
      · assumption
      · contradiction
      """

    # Task.ignore/1 must not leave the reply in the mailbox. On Elixir main
    # (638d17c) with OTP 29.1.2 this fails: the reply may arrive after
    # Task.ignore/1 checks for it and before demonitor/2 deactivates the
    # alias, and demonitor/2 only flushes DOWN-shaped messages. It holds once
    # Task.ignore/1 flushes the reply after demonitor/2.
    law ignore_drains_reply,
      expects: ignore_leaves_no_reply(),
      proof: ~LEAN"""
      -- lynx_counterexample reports a failing schedule quickly, before cbv
      -- evaluates every interleaving, which takes more than its default steps.
      have checked := Lynx.concurrent_of_check
        (Lynx.apply «ignore_drains_reply:ensures/0» Erlang.program.fun_table)
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 300
        (by lynx_counterexample; set_option cbv.maxSteps 1000000 in cbv) schedule
      split at checked
      · assumption
      · contradiction
      """
  end
end
