defmodule Lynx.Commands do
  @moduledoc "Invokes the Lean runner and Lake."

  @protocol_version "1.0"

  @doc """
  Runs a protocol request and collects its JSON updates in order.

  Each update includes rendered source, elapsed milliseconds, and diagnostics.
  Returns verification errors and skipped files as updates. Raises on failure responses,
  invalid JSON output, or unexpected exit statuses.
  The caller supplies the complete request, including its command and version.
  Updates retain the JSON protocol's string keys and values.
  """
  @spec runner!(String.t(), map()) :: [map()]
  def runner!(project_dir, request) do
    port = open_lake(project_dir, ["--quiet", "exe", "Lynx/Lynx.Runner"], [{:line, 1_000_000}])

    try do
      Port.command(port, JSON.encode!(request) <> "\n")
      collect_responses(port, [])
    after
      Port.close(port)
    end
  end

  @doc """
  Verifies assembled files and returns their source, timings, and diagnostics.

  Verification errors and skipped files are returned as updates. Runner failures raise.
  Reports and diagnostics have atom keys; statuses and severities are atoms.
  Module names, declarations, source, paths, and messages remain strings.
  Uses the current Mix build directory for cached artifacts, falling back to `_build/dev`.
  """
  @spec verify!(String.t(), [map()]) :: [Lynx.report()]
  def verify!(project_dir, files) when is_list(files) do
    runner!(project_dir, %{
      "command" => "verify",
      "version" => @protocol_version,
      "cache_dir" => cache_dir(),
      "files" => files
    })
    |> Enum.map(&Lynx.Runner.decode_verify!/1)
  end

  defp cache_dir do
    build_path =
      try do
        Mix.Project.build_path()
      rescue
        _ -> "_build/dev"
      catch
        _, _ -> "_build/dev"
      end

    Path.join(build_path, "lynx") |> Path.expand()
  end

  defp collect_responses(port, responses) do
    output = collect_response(port, [])

    response =
      case JSON.decode(output) do
        {:ok, response} ->
          response

        {:error, reason} ->
          raise "lynx runner returned invalid JSON (#{json_error(reason)}): #{inspect(output, printable_limit: 200)}"
      end

    case response do
      %{"status" => "failure", "message" => message} ->
        raise message

      %{"status" => "done"} ->
        Enum.reverse(responses)

      %{"status" => status} when is_binary(status) ->
        collect_responses(port, [response | responses])

      _ ->
        raise "lynx runner returned an unexpected response: #{output}"
    end
  end

  defp json_error({:unexpected_end, offset}), do: "input ends at byte #{offset}"
  defp json_error({:invalid_byte, offset, byte}), do: "invalid byte #{byte} at offset #{offset}"
  defp json_error(reason), do: inspect(reason)

  defp collect_response(port, chunks) do
    receive do
      {^port, {:data, {:eol, data}}} ->
        [data | chunks] |> Enum.reverse() |> IO.iodata_to_binary()

      {^port, {:data, {:noeol, data}}} ->
        collect_response(port, [data | chunks])

      {^port, {:exit_status, status}} ->
        raise "lynx runner exited with status #{status} before responding"
    end
  end

  @doc """
  Runs Lake and returns `{exit_status, stdout}`. Stderr is inherited.

  Uses the caller's active toolchain and selects `project_dir` with Lake's `--dir` option.
  Arguments are passed directly to the executable.

  Commands reading stdin must use framing (such as a terminating newline),
  since ports cannot close stdin alone.
  """
  @spec lake(String.t(), [String.t()], binary()) :: {non_neg_integer(), binary()}
  def lake(project_dir, args, stdin \\ "")
      when is_binary(project_dir) and is_list(args) and is_binary(stdin) do
    port = open_lake(project_dir, args)
    if stdin != "", do: Port.command(port, stdin)
    collect(port, [])
  end

  defp open_lake(project_dir, args, options \\ []) do
    executable =
      System.find_executable("lake") ||
        raise(
          "lake command line executable could not be found, make sure it is installed and available in $PATH"
        )

    project_dir = Path.expand(project_dir)

    Port.open(
      {:spawn_executable, String.to_charlist(executable)},
      [
        :binary,
        :exit_status,
        :use_stdio,
        :hide,
        args: ["--dir", project_dir | args]
      ] ++ options
    )
  end

  defp collect(port, chunks) do
    receive do
      {^port, {:data, data}} ->
        collect(port, [data | chunks])

      {^port, {:exit_status, status}} ->
        {status, chunks |> Enum.reverse() |> IO.iodata_to_binary()}
    end
  end
end
