# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/otp/queue.exs
# Prove the installed OTP queue module, translated from BEAM debug information.
# Checked against Erlang/OTP 29.1.2 (stdlib 8.1.1, ERTS 17.1.1).
# These proofs depend on implementation details; rerun after OTP upgrades.
ExUnit.start()

defmodule QueueProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  laws "queue" do
    law reverse_involution(queue),
      requires: :queue.is_queue(queue),
      expects: :queue.reverse(:queue.reverse(queue)) === queue,
      proof: ~LEAN"""
      cases queue <;> simp [«reverse_involution:requires/1», Erlang.queue.«is_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [Erlang.queue.«is_queue/1»] at requires
      | [rear, front] =>
        cases rear <;> simp [«reverse_involution:requires/1», Erlang.queue.«is_queue/1»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»] at requires
        all_goals cases front <;> simp [Erlang.erlang.«is_list/1»] at requires
        all_goals simp [«reverse_involution:ensures/1», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«and/2», Erlang.queue.«reverse/1», Erlang.erlang.«=:=/2»]
      """

    law reverse_exchanges_ends(value, queue),
      requires: :queue.is_queue(queue),
      expects:
        :queue.reverse(:queue.in(value, queue)) === :queue.in_r(value, :queue.reverse(queue)),
      proof: ~LEAN"""
      cases queue <;> simp [«reverse_exchanges_ends:requires/2», Erlang.queue.«is_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [Erlang.queue.«is_queue/1»] at requires
      | [rear, front] =>
        cases rear <;> simp [«reverse_exchanges_ends:requires/2», Erlang.queue.«is_queue/1»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»] at requires
        all_goals cases front <;> simp [Erlang.erlang.«is_list/1»] at requires
        all_goals simp [«reverse_exchanges_ends:ensures/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«and/2», Erlang.queue.«reverse/1», Erlang.queue.«in/2»,
          Erlang.queue.«in_r/2», Erlang.erlang.«=:=/2»]
        all_goals split <;> simp_all [Erlang.queue.«reverse/1», Erlang.queue.«in_r/2»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»,
          Erlang.erlang.«=:=/2»]
      """

    law front_insert_peek(value, queue),
      requires: :queue.is_queue(queue),
      expects: :queue.peek(:queue.in_r(value, queue)) === {:value, value},
      proof: ~LEAN"""
      cases queue <;> simp [«front_insert_peek:requires/2», Erlang.queue.«is_queue/1»] at requires
      rename_i fields
      rcases fields with ⟨fields⟩
      match fields with
      | [] | [_] | _ :: _ :: _ :: _ => simp [Erlang.queue.«is_queue/1»] at requires
      | [rear, front] =>
        cases rear <;> simp [«front_insert_peek:requires/2», Erlang.queue.«is_queue/1»,
          Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»] at requires
        all_goals cases front <;> simp [Erlang.erlang.«is_list/1»] at requires
        all_goals simp [«front_insert_peek:ensures/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«and/2», Erlang.queue.«in_r/2», Erlang.queue.«peek/1», Erlang.erlang.«=:=/2»]
        all_goals split <;> simp_all [Erlang.queue.«in_r/2»,
          Erlang.queue.«peek/1», Erlang.erlang.«is_list/1», Erlang.erlang.«and/2»,
          Erlang.erlang.«=:=/2»]
      """
  end
end
