defmodule Lynx.MixProject do
  use Mix.Project

  @source_url "https://github.com/josevalim/lynx"
  @version "0.2.0"

  def project do
    [
      app: :lynx,
      version: @version,
      name: "Lynx",
      description: "Formally verify Erlang/Elixir programs through embedded LEAN proofs",
      elixir: "~> 1.18",
      elixirc_paths: elixirc_paths(Mix.env()),
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      docs: docs(),
      package: package(),
      test_ignore_filters: ["test/fixtures/translations/regenerate.exs"],
      aliases: [
        compile: [&build_lean/1, "compile"],
        precommit: ["format", "test.all"],
        "test.lean": ["cmd --cd Lean lake test"],
        "test.all": ["test", "test.lean"],
        docs: [&register_lean_lexer/1, "docs"]
      ]
    ]
  end

  defp elixirc_paths(:test), do: ["lib", "test/support"]
  defp elixirc_paths(_), do: ["lib"]

  defp deps do
    [
      {:ex_doc, "~> 0.38", only: :docs},
      {:makeup_syntect, "~> 0.1", only: :docs}
    ]
  end

  defp docs do
    [
      main: "Lynx",
      logo: "logo.png",
      source_ref: "v#{@version}",
      source_url: @source_url
    ]
  end

  defp package do
    [
      licenses: ["Apache-2.0"],
      maintainers: ["José Valim"],
      links: %{"GitHub" => @source_url},
      files: [
        "lib",
        "src",
        "Lean",
        "examples/concurrency",
        "examples/elixir",
        "examples/deps",
        "lean-toolchain",
        ".formatter.exs",
        "mix.exs",
        "README.md",
        "LICENSE"
      ],
      exclude_patterns: [~r"^Lean/\.lake", ~r"^Lean/LynxTest"]
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

  # Highlights ```lean code blocks and ~LEAN sigils with the Lean grammar in
  # syntaxes/, which replaces the one bundled with makeup_syntect.
  # Syntect registers no languages on its own, so it does not replace other lexers.
  defp register_lean_lexer(_args) do
    Mix.Task.run("deps.loadpaths")
    Application.put_env(:makeup_syntect, :register_for_languages, [])

    Application.put_env(:makeup_syntect, :extra_syntax_folders, [
      Path.expand("syntaxes", __DIR__)
    ])

    {:ok, _} = Application.ensure_all_started([:makeup_elixir, :makeup_syntect])

    Makeup.Registry.register_lexer(MakeupSyntect.Lexer,
      options: [language: "lean"],
      names: ["lean"],
      extensions: ["lean"]
    )

    Makeup.Lexers.ElixirLexer.register_sigil_lexer("LEAN", MakeupSyntect.Lexer, language: "lean")
  end

  def cli do
    [
      preferred_envs: [
        "test.all": :test,
        precommit: :test,
        docs: :docs,
        "hex.publish": :docs
      ]
    ]
  end

  def application do
    [
      mod: {Lynx.Application, []},
      extra_applications: [:logger, :crypto]
    ]
  end
end
