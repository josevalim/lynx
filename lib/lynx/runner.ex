defmodule Lynx.Runner do
  @moduledoc false

  @statuses %{"ok" => :ok, "error" => :error, "skipped" => :skipped}
  @severities %{"error" => :error, "warning" => :warning, "information" => :information}

  @spec decode_verify!(map()) :: Lynx.Laws.report()
  def decode_verify!(%{
        "status" => status,
        "file" => file,
        "module" => module,
        "source" => source,
        "time_ms" => time,
        "cached" => cached,
        "diagnostics" => diagnostics
      })
      when status in ["ok", "error", "skipped"] and is_binary(file) and is_binary(module) and
             is_binary(source) and is_integer(time) and time >= 0 and is_boolean(cached) and
             is_list(diagnostics) do
    %{
      status: Map.fetch!(@statuses, status),
      file: file,
      module: module,
      source: source,
      time_ms: time,
      cached: cached,
      diagnostics: Enum.map(diagnostics, &decode_diagnostic!/1)
    }
  end

  def decode_verify!(response),
    do: raise("lynx runner returned an unexpected response: #{inspect(response)}")

  defp decode_diagnostic!(
         %{
           "file" => file,
           "module" => module,
           "declaration" => declaration,
           "severity" => severity,
           "message" => message
         } = diagnostic
       )
       when is_binary(file) and is_binary(module) and
              (is_binary(declaration) or is_nil(declaration)) and
              severity in ["error", "warning", "information"] and is_binary(message) do
    decoded = %{
      file: file,
      module: module,
      declaration: declaration,
      severity: Map.fetch!(@severities, severity),
      message: message
    }

    Enum.reduce([{"line", :line}, {"column", :column}], decoded, fn {key, atom}, decoded ->
      case Map.fetch(diagnostic, key) do
        :error -> decoded
        {:ok, value} when is_integer(value) and value > 0 -> Map.put(decoded, atom, value)
        _ -> raise "lynx runner returned an unexpected diagnostic: #{inspect(diagnostic)}"
      end
    end)
  end

  defp decode_diagnostic!(diagnostic),
    do: raise("lynx runner returned an unexpected diagnostic: #{inspect(diagnostic)}")
end
