# mix run examples/errors/invalid_proof.exs
ExUnit.start()

defmodule InvalidProofTest do
  use ExUnit.Case
  use Lynx.Case

  laws "invalid proof" do
    # The expectation is true, but the Lean proof has an unclosed parenthesis.
    law true_is_true,
      expects: true,
      proof: ~LEAN"exact ("
  end
end
