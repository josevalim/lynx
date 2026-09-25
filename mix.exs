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

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      # {:dep_from_hexpm, "~> 0.3.0"},
      # {:dep_from_git, git: "https://github.com/elixir-lang/my_dep.git", tag: "0.1.0"}
    ]
  end
end
