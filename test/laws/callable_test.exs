defmodule Lynx.Laws.CallableTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  law checked(value),
    requires: value,
    expects: value,
    proof: ~LEAN"exact requires"

  test "laws remain callable and are registered with ExUnit" do
    assert checked(true)

    assert_raise ArgumentError, "law checked/1 requires returned false", fn ->
      checked(false)
    end

    assert [%{name: :"law checked/1", tags: tags}] =
             Enum.filter(__MODULE__.__ex_unit__().tests, &(&1.tags.test_type == :law))

    assert tags.file == __ENV__.file
    assert tags.line == 5
  end
end
