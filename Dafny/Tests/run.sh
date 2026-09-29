#!/bin/sh
set -eu
daxie_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
. "$daxie_root/tools.sh"
rm -rf "$daxie_root/.build"
setup_dotnet
cd "$daxie_root"
"$DAFNY" verify dfyconfig.toml
mkdir -p .build/packages
"$DAFNY" translate cs Tests/Semantics.dfy --no-verify --include-runtime --output .build/Semantics
# The SDK provides everything the generated runtime needs; no package references.
cat > .build/Semantics.csproj <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net8.0</TargetFramework>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
  </PropertyGroup>
  <ItemGroup><Compile Include="Semantics.cs" /></ItemGroup>
</Project>
EOF
"$DOTNET" build .build/Semantics.csproj --nologo --verbosity quiet \
  --source "$daxie_root/.build/packages" -p:NuGetAudit=false \
  --output "$daxie_root/.build/tests"
"$DOTNET" "$daxie_root/.build/tests/Semantics.dll"
