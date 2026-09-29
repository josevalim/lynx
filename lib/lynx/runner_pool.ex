defmodule Lynx.RunnerPool do
  @moduledoc false

  @behaviour NimblePool

  @registry Lynx.RunnerRegistry
  @supervisor Lynx.RunnerSupervisor
  @runner Path.expand("../../Lean/Lynx/Runner.lean", __DIR__)

  @doc """
  Sends one request map to a pooled Lean runner and returns its decoded response.

  Verification errors are returned with their diagnostics. Runner failures and
  malformed responses raise. Pools are keyed by `project_dir` and start ports lazily.
  """
  @spec command(String.t(), map()) :: map()
  def command(project_dir, request) when is_binary(project_dir) and is_map(request) do
    payload = JSON.encode!(request)
    pool = {:via, Registry, {@registry, project_dir}}
    ensure_pool(project_dir, pool)

    output =
      NimblePool.checkout!(
        pool,
        :checkout,
        fn _from, port ->
          send(port, {self(), {:command, payload <> "\n"}})
          output = response(port, "")

          try do
            Process.unlink(port)
            {output, :ok}
          rescue
            _ -> {output, :close}
          end
        end,
        :infinity
      )

    decoded =
      case JSON.decode(output) do
        {:ok, decoded} ->
          decoded

        {:error, reason} ->
          raise "lynx runner returned invalid JSON (#{json_error(reason)}): #{inspect(output, printable_limit: 200)}"
      end

    case decoded do
      %{"status" => "failure", "message" => message} -> raise message
      %{"status" => "ok"} -> decoded
      %{"status" => "error"} -> decoded
      _ -> raise "lynx runner returned an unexpected response: #{output}"
    end
  end

  defp json_error({:unexpected_end, offset}), do: "input ends at byte #{offset}"
  defp json_error({:invalid_byte, offset, byte}), do: "invalid byte #{byte} at offset #{offset}"
  defp json_error(reason), do: inspect(reason)

  defp ensure_pool(project_dir, pool) do
    if Registry.lookup(@registry, project_dir) == [] do
      unless File.dir?(project_dir) do
        raise ArgumentError, "lynx project directory does not exist: #{project_dir}"
      end

      lake =
        System.find_executable("lake") ||
          raise "lake command line executable could not be found, make sure it is installed and available in $PATH"

      spec =
        NimblePool.child_spec(
          worker: {__MODULE__, {project_dir, lake}},
          name: pool,
          pool_size: System.schedulers_online(),
          lazy: true
        )

      case DynamicSupervisor.start_child(@supervisor, spec) do
        {:ok, _pid} -> :ok
        {:error, {:already_started, _pid}} -> :ok
        {:error, reason} -> raise "could not start lynx runner pool: #{inspect(reason)}"
      end
    end
  end

  @impl NimblePool
  def init_worker({project_dir, lake} = pool_state) do
    port =
      Port.open(
        {:spawn_executable, String.to_charlist(lake)},
        [
          :binary,
          :exit_status,
          :use_stdio,
          :hide,
          {:line, 1_000_000},
          cd: project_dir,
          args: ["env", "lean", "--run", @runner]
        ]
      )

    {:ok, port, pool_state}
  end

  @impl NimblePool
  def handle_checkout(:checkout, {pid, _ref}, port, pool_state) do
    Port.connect(port, pid)
    {:ok, port, port, pool_state}
  end

  @impl NimblePool
  # Extension-loaded imports cannot safely free their compacted regions. Recycle
  # the process so each request starts with an independent Lean environment.
  def handle_checkin(:ok, _from, _port, pool_state), do: {:remove, :completed, pool_state}
  def handle_checkin(:close, _from, _port, pool_state), do: {:remove, :closed, pool_state}

  @impl NimblePool
  def terminate_worker(_reason, port, pool_state) do
    try do
      Port.close(port)
    rescue
      _ -> :ok
    end

    {:ok, pool_state}
  end

  defp response(port, chunks) do
    receive do
      {^port, {:data, {:eol, data}}} ->
        chunks <> data

      {^port, {:data, {:noeol, data}}} ->
        response(port, chunks <> data)

      {^port, {:exit_status, status}} ->
        raise "lynx runner exited with status #{status} before responding"
    end
  end
end
