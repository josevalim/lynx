defmodule Lynx.Bytecode do
  @moduledoc false
  use Agent

  def start_link(_opts) do
    Agent.start_link(fn -> %{} end, name: __MODULE__)
  end

  def put(module, beam) when is_atom(module) and is_binary(beam) do
    Agent.update(__MODULE__, &Map.put(&1, module, beam))
  end

  def fetch!(module) do
    case Agent.get(__MODULE__, &Map.fetch(&1, module)) do
      {:ok, beam} -> beam
      :error -> raise KeyError, key: module
    end
  end
end
