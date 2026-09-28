defmodule Lynx.MixProject do
  use Mix.Project

  def project do
    [
      app: :lynx,
      version: "0.1.0",
      elixir: "~> 1.18",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      aliases: [
        setup: ["deps.get", "cmd --cd Lean lake build"],
        precommit: ["format", "test.all"],
        "test.lean": ["cmd --cd Lean lake test"],
        "test.all": ["test", "test.lean"]
      ]
    ]
  end

  def cli do
    [preferred_envs: ["test.all": :test, precommit: :test]]
  end

  def application do
    [
      mod: {Lynx.Application, []},
      extra_applications: [:logger]
    ]
  end

  defp deps do
    [
      {:nimble_pool, "~> 1.0"}
    ]
  end
end
