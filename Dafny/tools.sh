# Shared by the shell runners; callers set daxie_root first.
if [ -z "${DAFNY:-}" ]; then
  if [ -x "$HOME/.dafny/bin/dafny" ]; then
    DAFNY="$HOME/.dafny/bin/dafny"
  else
    DAFNY=dafny
  fi
fi

setup_dotnet() {
  if [ -z "${DOTNET:-}" ]; then
    if command -v dotnet >/dev/null 2>&1; then
      DOTNET=dotnet
    else
      echo 'Set DOTNET to the .NET 8 SDK executable.' >&2
      exit 1
    fi
  fi
  # Keep SDK first-run state and package caches within this project.
  export DOTNET_CLI_HOME="$daxie_root/.build/dotnet-home"
  export NUGET_PACKAGES="$daxie_root/.build/packages"
  export NUGET_HTTP_CACHE_PATH="$daxie_root/.build/http-cache"
  export DOTNET_CLI_TELEMETRY_OPTOUT=1
  export DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1
  export DOTNET_NOLOGO=1
  export DOTNET_GENERATE_ASPNET_CERTIFICATE=false
  export DOTNET_ADD_GLOBAL_TOOLS_TO_PATH=false
}
