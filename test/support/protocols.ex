# Protocols and implementations compiled with the project, so they are
# consolidated and their dispatch can be translated from the code path.

defprotocol Lynx.Support.Size do
  def size(data)
end

defmodule Lynx.Support.Point do
  defstruct [:x, :y]
end

defimpl Lynx.Support.Size, for: List do
  def size(list), do: length(list)
end

defimpl Lynx.Support.Size, for: Integer do
  def size(_integer), do: 1
end

# Structs dispatch to their own implementation, never to the one for maps.
defimpl Lynx.Support.Size, for: Map do
  def size(map), do: map_size(map)
end

defimpl Lynx.Support.Size, for: Lynx.Support.Point do
  def size(_point), do: 2
end

defprotocol Lynx.Support.Describe do
  @fallback_to_any true
  def describe(data, prefix)
end

defimpl Lynx.Support.Describe, for: Any do
  def describe(_data, prefix), do: {prefix, :any}
end

defimpl Lynx.Support.Describe, for: Atom do
  def describe(atom, prefix), do: {prefix, atom}
end

defmodule Lynx.Support.Tagged do
  @derive Lynx.Support.Describe
  defstruct [:tag]
end
