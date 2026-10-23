defmodule Lynx.MixProject do
  use Mix.Project

  def project do
    [
      app: :lynx,
      version: "0.1.0",
      elixir: "~> 1.18",
      start_permanent: Mix.env() == :prod,
      deps: [],
      test_ignore_filters: ["test/fixtures/translations/regenerate.exs"],
      aliases: [
        compile: [&build_lean/1, "compile"],
        precommit: ["format", "test.all"],
        "test.lean": ["cmd --cd Lean lake test"],
        "test.all": ["test", "test.lean"]
      ]
    ]
  end

  defp build_lean(_args) do
    lean_dir = Path.join(__DIR__, "Lean")
    lock_dir = Mix.Project.config()[:lockfile] |> Path.expand() |> Path.dirname()

    # The runner is not a default target, so `lake check` covers only the library.
    args = ["--dir", lean_dir, "build", "Lynx", "Lynx.Runner"]

    # Port output may split multibyte characters, so let Lake write directly.
    case Mix.shell().cmd({"lake", args}, cd: lock_dir, use_stdio: false) do
      0 -> :ok
      status -> Mix.raise("Lake build failed with status #{status}")
    end
  end

  def cli do
    [preferred_envs: ["test.all": :test, precommit: :test]]
  end

  def application do
    [
      mod: {Lynx.Application, []},
      extra_applications: [:logger, :crypto]
    ]
  end
end
