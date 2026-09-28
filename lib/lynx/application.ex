defmodule Lynx.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {Registry, keys: :unique, name: Lynx.RunnerRegistry},
      {DynamicSupervisor, strategy: :one_for_one, name: Lynx.RunnerSupervisor}
    ]

    Supervisor.start_link(children, strategy: :one_for_one, name: Lynx.Supervisor)
  end
end
