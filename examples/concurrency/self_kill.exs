# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/concurrency/self_kill.exs
#
# A linked child sends itself an exit signal, then tells its trapping parent
# that it survived. With :erlang.exit/2, the child ends before the call
# returns, so the parent always gets its exit reason. With
# :erlang.exit_signal/2, the child acts on its own signal later, so either
# message may arrive first.
ExUnit.start()

defmodule SelfKillProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def self_kill do
    parent = self()
    Process.flag(:trap_exit, true)

    child =
      spawn_link(fn ->
        :erlang.exit(self(), :alma)
        send(parent, :survived)
      end)

    receive do
      :survived -> :erlang.error(:oops)
      {:EXIT, ^child, :alma} -> :ok
    end
  end

  def self_signal do
    parent = self()
    Process.flag(:trap_exit, true)

    child =
      spawn_link(fn ->
        :erlang.exit_signal(self(), :alma)
        send(parent, :survived)
      end)

    receive do
      :survived -> :ok
      {:EXIT, ^child, :alma} -> :ok
    end
  end

  laws "self kill" do
    law self_kill_is_final,
      expects: self_kill() == :ok,
      proof: ~LEAN"""
      -- Spawning the child calls its function one level down, and the
      -- parent's receive runs one level further down.
      refine ⟨2, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      -- Evaluate every interleaving: the child dies before it can send.
      exact Lynx.concurrent_of_check
        (Lynx.apply «self_kill_is_final:ensures/0» Erlang.program.fun_table (depth + 2))
        Lynx.Outcome.isTrue 64
        (fun _ => by lynx_kernel)
        fun _ => Lynx.Outcome.eq_of_isTrue
      """

    law self_signal_is_ok,
      expects: self_signal() == :ok,
      proof: ~LEAN"""
      refine ⟨2, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      exact Lynx.concurrent_of_check
        (Lynx.apply «self_signal_is_ok:ensures/0» Erlang.program.fun_table (depth + 2))
        Lynx.Outcome.isTrue 64
        (fun _ => by lynx_kernel)
        fun _ => Lynx.Outcome.eq_of_isTrue
      """
  end
end
