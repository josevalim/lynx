defmodule Lynx.LawsTest do
  use ExUnit.Case, async: true

  describe "evaluation" do
    test "laws return true or raise with the invalid predicate value" do
      defmodule Callable do
        use Lynx.Laws

        law checked(x), requires: x, expects: true
        law expected(x), expects: x
        law pair(a, b), requires: a, expects: b
      end

      assert Callable.checked(true)
      assert Callable.expected(true)
      assert Callable.pair(true, true)

      for {function, args, exception, message} <- [
            {:pair, [false, true], ArgumentError, "law pair/2 requires returned false"},
            {:pair, [true, false], RuntimeError, "law pair/2 expects returned false"},
            {:checked, [false], ArgumentError, "law checked/1 requires returned false"},
            {:checked, [:invalid], ArgumentError, "law checked/1 requires returned :invalid"},
            {:expected, [false], RuntimeError, "law expected/1 expects returned false"},
            {:expected, [42], RuntimeError, "law expected/1 expects returned 42"}
          ] do
        assert_raise exception, message, fn -> apply(Callable, function, args) end
      end
    end

    test "a failed precondition does not evaluate the expected expression" do
      defmodule Precondition do
        use Lynx.Laws
        law checked, requires: false, expects: send(self(), :evaluated)
      end

      assert_raise ArgumentError, fn -> Precondition.checked() end
      refute_received :evaluated
    end
  end

  describe "reflection" do
    test "persists law metadata and keeps predicate helpers private" do
      defmodule Reflection do
        use Lynx.Laws

        law checked(x), requires: x, expects: true
        law expected(x), expects: x
        law pair(a, b), requires: a, expects: b
      end

      assert Reflection.__info__(:functions) == [checked: 1, expected: 1, pair: 2]

      assert [
               %{
                 name: {:checked, [:x]},
                 requires: :"checked:requires",
                 ensures: :"checked:ensures",
                 proof: %{source: "rfl", indentation: 0}
               },
               %{name: {:expected, [:x]}, ensures: :"expected:ensures"} = expected,
               %{name: {:pair, [:a, :b]}}
             ] = laws(Reflection)

      refute Map.has_key?(expected, :requires)
      refute Map.has_key?(expected, :indentation)
    end

    test "preserves inline proof positions" do
      line = __ENV__.line + 4

      defmodule Inline do
        use Lynx.Laws
        law checked(x), expects: x, proof: ~LEAN"rfl"
      end

      assert [%{span: {^line, 13}, proof: %{source: "rfl", indentation: 0, span: {^line, 50}}}] =
               laws(Inline)
    end

    test "preserves heredoc proof positions and indentation" do
      line = __ENV__.line + 8

      defmodule Heredoc do
        use Lynx.Laws

        law checked(x),
          expects: x,
          proof: ~LEAN"""
          rfl
          """
      end

      call_line = line - 3

      assert [
               %{
                 span: {^call_line, 13},
                 proof: %{source: "rfl\n", indentation: 10, span: {^line, 11}}
               }
             ] = laws(Heredoc)
    end
  end

  describe "errors" do
    test "requires local calls with unique named variable arguments" do
      for {call, reason} <- [
            {quote(do: Other.checked(x)), "law must be a local function call"},
            {quote(do: checked(1)), "law arguments must be named variables"},
            {quote(do: checked({x, y})), "law arguments must be named variables"},
            {quote(do: checked(_)), "law arguments must be named variables"},
            {quote(do: checked(x, x)), "law arguments must be unique"}
          ] do
        error =
          assert_raise CompileError, fn ->
            Code.eval_quoted(
              quote do
                defmodule InvalidArguments do
                  use Lynx.Laws
                  law unquote(call), expects: true
                end
              end
            )
          end

        assert %CompileError{description: ^reason} = error
      end
    end

    test "requires an expectation and a literal proof sigil" do
      for {options, reason} <- [
            {:invalid, "law options must be a keyword list"},
            {[requires: true], "law requires the :expects option to be given"},
            {[expects: true, proof: "rfl"],
             "proof must be a literal ~LEAN sigil without modifiers"},
            {quote(do: [expects: true, proof: ~LEAN"rfl"x]),
             "proof must be a literal ~LEAN sigil without modifiers"}
          ] do
        error =
          assert_raise CompileError, fn ->
            Code.eval_quoted(
              quote do
                defmodule InvalidOptions do
                  use Lynx.Laws
                  law checked, unquote(options)
                end
              end
            )
          end

        assert %CompileError{description: ^reason} = error
      end
    end
  end

  describe "translation" do
    test "translates predicates and recursively includes their callees" do
      {:module, module, beam, _} =
        defmodule Predicates do
          @compile :debug_info
          use Lynx.Laws
          law checked(a, b), requires: allowed(a), expects: identity(b)
          defp allowed(value), do: identity(value)
          defp identity(value), do: value
          def unused(value), do: {:unsupported, value}
        end

      assert [
               %{
                 "contents" => [
                   %{
                     "kind" => "def",
                     "name" => "identity",
                     "params" => [%{"name" => 0}],
                     "pure" => true,
                     "body" => %{"kind" => "return", "value" => %{"kind" => "var", "name" => 0}}
                   },
                   %{"kind" => "def", "name" => "allowed", "params" => [_], "pure" => true},
                   %{
                     "kind" => "def",
                     "name" => "checked:ensures",
                     "params" => [%{"name" => 0}, %{"name" => 1}],
                     "pure" => true,
                     "body" => %{
                       "kind" => "local_call",
                       "name" => "identity",
                       "args" => [%{"kind" => "var", "name" => 1}]
                     }
                   },
                   %{
                     "kind" => "def",
                     "name" => "checked:requires",
                     "params" => [%{"name" => 0}, %{"name" => 1}],
                     "pure" => true,
                     "body" => %{
                       "kind" => "local_call",
                       "name" => "allowed",
                       "args" => [%{"kind" => "var", "name" => 0}]
                     }
                   },
                   %{
                     "kind" => "theorem",
                     "name" => "checked",
                     "params" => ["a", "b"],
                     "requires" => "checked:requires",
                     "ensures" => "checked:ensures",
                     "proof" => %{"source" => "rfl", "indentation" => 0}
                   }
                 ]
               }
             ] = translate(module, beam)
    end

    test "translates every law and omits unused default preconditions" do
      {:module, module, beam, _} =
        defmodule Unconditional do
          @compile :debug_info
          use Lynx.Laws
          law first(x), expects: x
          law second, expects: true
        end

      assert [
               %{
                 "contents" => [
                   %{
                     "kind" => "def",
                     "name" => "first:ensures",
                     "params" => [_],
                     "body" => %{"kind" => "return", "value" => %{"kind" => "var", "name" => 0}}
                   },
                   %{
                     "kind" => "def",
                     "name" => "second:ensures",
                     "params" => [],
                     "body" => %{
                       "kind" => "return",
                       "value" => %{"kind" => "atom", "value" => "true"}
                     }
                   },
                   %{
                     "kind" => "theorem",
                     "name" => "first",
                     "params" => ["x"],
                     "ensures" => "first:ensures",
                     "proof" => %{"source" => "rfl"}
                   } = first,
                   %{
                     "kind" => "theorem",
                     "name" => "second",
                     "params" => [],
                     "ensures" => "second:ensures",
                     "proof" => %{"source" => "rfl"}
                   } = second
                 ]
               }
             ] = translate(module, beam)

      refute Map.has_key?(first, "requires")
      refute Map.has_key?(second, "requires")
    end
  end

  defp translate(module, beam) do
    translation =
      Lynx.Translation.new() |> Lynx.Translation.add(beam) |> Lynx.Translation.verify(module)

    assert Map.has_key?(translation.modules, module)
    Lynx.Translation.assemble(translation)
  end

  defp laws(module) do
    for {:law, entries} <- module.__info__(:attributes), entry <- entries, do: entry
  end
end
