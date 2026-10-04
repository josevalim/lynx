defmodule Lynx.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    Supervisor.start_link([Lynx.Bytecode], strategy: :one_for_one, name: Lynx.Supervisor)
  end
end
