# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/concurrency/workers.exs
#
# Two workers race to report to their parent, so the parent receives their
# results in either order. The sum is the same under every schedule. The
# program has no inputs, so the proof evaluates every interleaving with
# Lynx.concurrent_of_check.
ExUnit.start()

defmodule WorkersProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  def sum_workers do
    parent = self()
    spawn(fn -> send(parent, 1) end)
    spawn(fn -> send(parent, 2) end)

    receive do
      first ->
        receive do
          second -> first + second
        end
    end
  end

  laws "workers" do
    law sum_workers_is_three,
      expects: sum_workers() == 3,
      proof: ~LEAN"""
      -- Evaluate every interleaving: the workers report in either order.
      have checked := Lynx.concurrent_of_check
        (Lynx.apply «sum_workers_is_three:ensures/0» Erlang.program.fun_table)
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 64 (by cbv) schedule
      split at checked
      · assumption
      · contradiction
      """
  end
end
