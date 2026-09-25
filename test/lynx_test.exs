defmodule LynxTest do
  use ExUnit.Case
  doctest Lynx

  test "greets the world" do
    assert Lynx.hello() == :world
  end
end
