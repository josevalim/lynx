# LYNX_PROFILE=1 LYNX_CACHE=0 mix run examples/errors/deadlock.exs
ExUnit.start()

defmodule DeadlockTest do
  use ExUnit.Case
  use Lynx.Case

  def await_reply do
    receive do
      :reply -> :ok
    end
  end

  laws "deadlock" do
    # There is no sender and no timeout, so this receive waits forever.
    law receives_reply,
      expects: await_reply() == :ok,
      proof: ~LEAN"""
      simp [«receives_reply:ensures/0», «await_reply/0»,
        Lynx.Result.receiveWith, Lynx.ReceiveTimeout.ofTerm]
      """
  end
end
