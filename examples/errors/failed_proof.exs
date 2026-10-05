# mix run examples/errors/failed_proof.exs
ExUnit.start()

defmodule FailedProofTest do
  use ExUnit.Case
  use Lynx.Case

  laws "failed proof" do
    # This false expectation cannot be proved by reflexivity.
    law false_is_true,
      expects: false,
      proof: ~LEAN"rfl"
  end
end
