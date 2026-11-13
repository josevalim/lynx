# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/elixir/task.exs
#
# Task.async/1 and Task.await/2 compute in a linked process and reply through
# a monitor alias. Awaiting without a timeout returns the task's result in
# every run, and awaiting with one either returns it or times out. The
# input is an arbitrary integer, but the processes take the same steps for
# every value, so the proofs evaluate every interleaving. Ignoring a task, or
# awaiting one until it times out, leaves its reply out of the owner's inbox.
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

  def await_leaves_no_reply do
    task = Task.async(fn -> :reply end)

    result =
      try do
        Task.await(task, 100)
      catch
        :exit, {:timeout, _} -> :timeout
      end

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

    result in [:reply, :timeout] and empty?
  end

  laws "Task" do
    prelude ~LEAN"""
    module

    public import Lynx

    public section

    namespace TaskProof

    /-! `cbv` cannot decide `n * 2 < n * 2` for a symbolic `n`, so it compares
    a number with itself by these lemmas instead. -/

    @[cbv_eval] theorem compare_int_self (a : Int) : compareOfLessAndEq a a = .eq := by
      simp [compareOfLessAndEq]

    @[cbv_eval] theorem compare_rat_self (a : Rat) : compareOfLessAndEq a a = .eq := by
      simp [compareOfLessAndEq]

    end TaskProof
    """

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
        cases x <;> simp [«double_in_task_doubles:requires/1», Erlang.erlang.«is_integer/1»] at requires ⊢
      -- The task is spawned, receives its work, and applies its function
      -- through :erlang.apply/2, each one level down.
      refine ⟨4, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      -- Evaluate every interleaving; only the final comparison depends on n.
      exact Lynx.concurrent_of_check
        (Lynx.apply «double_in_task_doubles:ensures/1» Erlang.program.fun_table (depth + 4) (.integer n))
        Lynx.Outcome.isTrue 300
        (fun _ => by cbv)
        fun _ => Lynx.Outcome.eq_of_isTrue
      """

    law double_or_timeout_doubles(x),
      requires: is_integer(x),
      expects: double_or_timeout(x) in [x * 2, :timeout],
      proof: ~LEAN"""
      obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
        cases x <;> simp [«double_or_timeout_doubles:requires/1», Erlang.erlang.«is_integer/1»] at requires ⊢
      -- The task is spawned, receives its work, and applies its function
      -- through :erlang.apply/2, each one level down.
      refine ⟨4, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      -- The timeout may expire before or after the reply arrives. When the
      -- reply wins, the owner compares n * 2 with itself, which cbv decides
      -- with TaskProof.compare_int_self.
      exact Lynx.concurrent_of_check
        (Lynx.apply «double_or_timeout_doubles:ensures/1» Erlang.program.fun_table (depth + 4) (.integer n))
        Lynx.Outcome.isTrue 300
        (fun _ => by cbv)
        fun _ => Lynx.Outcome.eq_of_isTrue
      """

    # Task.ignore/1 must not leave the reply in the mailbox. On Elixir main
    # (638d17c) with OTP 29.1.2 this fails: the reply may arrive after
    # Task.ignore/1 checks for it and before demonitor/2 deactivates the
    # alias, and demonitor/2 only flushes DOWN-shaped messages. It holds once
    # Task.ignore/1 flushes the reply after demonitor/2.
    law ignore_drains_reply,
      expects: ignore_leaves_no_reply(),
      proof: ~LEAN"""
      -- The task is spawned, receives its work, and applies its function
      -- through :erlang.apply/2, each one level down.
      refine ⟨4, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      -- lynx_counterexample reports a failing schedule quickly, before the
      -- kernel evaluates every interleaving.
      exact Lynx.concurrent_of_check
        (Lynx.apply «ignore_drains_reply:ensures/0» Erlang.program.fun_table (depth + 4))
        Lynx.Outcome.isTrue 300
        (fun _ => by lynx_counterexample; lynx_kernel)
        fun _ => Lynx.Outcome.eq_of_isTrue
      """
  end

  laws "Task.await" do
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

    # Task.await/2 must not leave the reply in the mailbox when it times out.
    # On Elixir main (9636fee) with OTP 29.1.2 this fails: the reply may arrive
    # at the alias after the timeout and before demonitor/2 deactivates it,
    # and demonitor/2 only flushes DOWN-shaped messages. It holds once
    # Task.await/2 flushes the reply after demonitor/2.
    law await_drains_reply,
      expects: await_leaves_no_reply(),
      proof: ~LEAN"""
      -- The task is spawned, receives its work, and applies its function
      -- through :erlang.apply/2, each one level down.
      refine ⟨4, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      exact Lynx.concurrent_of_check
        (Lynx.apply «await_drains_reply:ensures/0» Erlang.program.fun_table (depth + 4))
        Lynx.Outcome.isTrue 300
        (fun _ => by lynx_counterexample; lynx_kernel)
        fun _ => Lynx.Outcome.eq_of_isTrue
      """
  end
end
