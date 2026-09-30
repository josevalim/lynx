#!/bin/sh
: "${FSTAR:=fstar.exe}"
: "${OCAMLFIND:=ocamlfind}"
if [ -z "${Z3:-}" ]; then
  if command -v z3-4.13.3 >/dev/null 2>&1; then Z3=$(command -v z3-4.13.3)
  elif [ -x "$HOME/.dafny/bin/z3/bin/z3-4.16.0" ]; then Z3="$HOME/.dafny/bin/z3/bin/z3-4.16.0"
  else Z3=$(command -v z3) || { echo 'Set Z3 to a Z3 executable.' >&2; exit 1; }; fi
fi
Z3_VERSION=$("$Z3" --version | awk '{print $3}')
foxy_check() {
  set -- "$FSTAR" --smt "$Z3" --z3version "$Z3_VERSION" --cache_dir .build/cache \
    --include Foxy --include Tests --include Benchmarks "$@"
  if [ -n "${FOXY_TIME_OUTPUT:-}" ]; then
    /usr/bin/time -p -o "$FOXY_TIME_OUTPUT" "$@"
  else
    "$@"
  fi
}
