#!/bin/sh
set -eu
foxy_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$foxy_root"
. ./tools.sh
# All caches, extracted source, and binaries are regenerated from project source.
rm -rf .build
mkdir -p .build/cache .build/ocaml
sh verify.sh
for probe in RecursiveClosure FunctionEquality; do
  if foxy_check "Tests/Rejected/Foxy.Rejected.$probe.fst" > ".build/$probe.log" 2>&1; then
    echo "Expected $probe to be rejected" >&2; exit 1
  fi
  case "$probe" in
    RecursiveClosure) expected='strict positivity' ;;
    FunctionEquality) expected='Expected type Prims.eqtype' ;;
  esac
  if ! grep -F "$expected" ".build/$probe.log" >/dev/null; then
    cat ".build/$probe.log" >&2; exit 1
  fi
done
foxy_check --codegen OCaml --extract Foxy --odir .build/ocaml Tests/Foxy.Tests.Main.fst
cd .build/ocaml
# ocamldep supplies dependency order for the compiler-generated files.
"$OCAMLFIND" ocamlopt -package fstar.lib -linkpkg -w -a $(ocamldep -sort ./*.ml) -o semantic-tests
./semantic-tests
