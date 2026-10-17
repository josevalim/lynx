defmodule Lynx.Integration.CaseTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  @tag selected: true
  laws "dependent laws" do
    law z_checked(value),
      requires: value,
      expects: value,
      proof: ~LEAN"exact requires"

    law a_checked(value),
      requires: value,
      expects: value,
      proof: ~LEAN"exact «z_checked/1» value requires"
  end

  laws "unconditional laws" do
    law unconditional, expects: true
  end

  test "laws remain callable" do
    assert z_checked(true)
    assert a_checked(true)
    assert unconditional()

    assert_raise ArgumentError, "law z_checked/1 requires returned false", fn ->
      z_checked(false)
    end
  end

  test "tags apply only to the following group" do
    groups = Enum.filter(__MODULE__.__ex_unit__().tests, &(&1.tags.test_type == :laws))
    assert [dependent, unconditional] = groups
    assert dependent.name == :"laws dependent laws"
    assert dependent.tags.laws
    assert dependent.tags.file == __ENV__.file
    assert dependent.tags.line == 6
    assert dependent.tags.selected
    assert unconditional.name == :"laws unconditional laws"
    refute Map.has_key?(unconditional.tags, :selected)

    for test <- __MODULE__.__ex_unit__().tests, test.tags.test_type == :test do
      refute Map.has_key?(test.tags, :selected)
      refute Map.has_key?(test.tags, :laws)
    end

    assert is_binary(Lynx.Bytecode.fetch!(__MODULE__))
  end
end
