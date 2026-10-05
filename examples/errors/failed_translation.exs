# mix run examples/errors/failed_translation.exs
ExUnit.start()

defmodule FailedTranslationTest do
  use ExUnit.Case
  use Lynx.Case

  # Loading native code is not supported by the translator.
  def load_native_code, do: :erlang.load_nif(~c"example_nif", 0)

  laws "failed translation" do
    law load_nif_succeeds,
      expects: load_native_code() == :ok,
      proof: ~LEAN"rfl"
  end
end
