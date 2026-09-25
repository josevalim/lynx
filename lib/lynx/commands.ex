defmodule Lynx.Commands do
  @moduledoc false

  @runner Path.expand("../../Lean/Lynx/Runner.lean", __DIR__)

  @doc """
  Runs a Runner command with JSON input and returns the decoded response.

  Returns verification errors with their diagnostics. Raises on failure responses,
  invalid JSON output, or unexpected exit statuses.
  A newline is appended to stdin to terminate the request.
  """
  @spec runner!(String.t(), String.t(), binary()) :: map()
  def runner!(project_dir, command_type, stdin) do
    {status, output} =
      lake(project_dir, ["env", "lean", "--run", @runner, command_type], stdin <> "\n")

    response = JSON.decode!(output)

    case {status, response} do
      {_, %{"status" => "failure", "message" => message}} ->
        raise message

      {0, %{"status" => "ok"}} ->
        response

      {1, %{"status" => "error"}} ->
        response

      _ ->
        raise "Unexpected Runner #{command_type} response with exit status #{status}: #{output}"
    end
  end

  @doc """
  Runs Lake and returns `{exit_status, stdout}`. Stderr is inherited.

  Starts in `project_dir`, so Elan selects that project's toolchain.
  Arguments are passed directly to the executable.

  Commands reading stdin must use framing (such as a terminating newline),
  since ports cannot close stdin alone.
  """
  @spec lake(String.t(), [String.t()], binary()) :: {non_neg_integer(), binary()}
  def lake(project_dir, args, stdin \\ "")
      when is_binary(project_dir) and is_list(args) and is_binary(stdin) do
    executable =
      System.find_executable("lake") ||
        raise(
          "lake command line executable could not be found, make sure it is installed and available in $PATH"
        )

    port =
      Port.open(
        {:spawn_executable, String.to_charlist(executable)},
        [:binary, :exit_status, :use_stdio, :hide, cd: project_dir, args: args]
      )

    if stdin != "", do: Port.command(port, stdin)
    collect(port, [])
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
