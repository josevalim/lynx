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
        compile: ["cmd --cd Lean lake build", "compile"],
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
      extra_applications: [:logger, :crypto]
    ]
  end
end
