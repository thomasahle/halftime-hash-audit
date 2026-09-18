#!/usr/bin/env bash
# Native arm64 Mac, sequential single-process checks; no wide key experiment.
set -euo pipefail
cd "$(dirname "$0")/../.."
cert_dir=review-support/wrapper-cert
ulimit -c 0
uname -a > "$cert_dir/mac-environment.log"
clang++ --version >> "$cert_dir/mac-environment.log"
shasum -a 256 halftime-current.hpp halftime-current.tex >> "$cert_dir/mac-environment.log"

if nice -n 10 clang++ -std=c++17 -fsyntax-only "$cert_dir/include-only.cpp" \
   > "$cert_dir/neon-unmodified-build.log" 2>&1; then
  echo "ERROR: the recorded stock NEON dispatch failure was expected" >&2
  exit 1
fi

nice -n 10 clang++ -std=c++17 -O2 -U__ARM_NEON -U__ARM_NEON__ \
  "$cert_dir/header-check.cpp" -o "$cert_dir/header-check-scalar" \
  > "$cert_dir/scalar-build.log" 2>&1
nice -n 10 "$cert_dir/header-check-scalar" > "$cert_dir/scalar.log"

nice -n 10 clang++ -std=c++17 -O2 -fwrapv -DNEON_DISPATCH_ALIASES \
  "$cert_dir/header-check.cpp" -o "$cert_dir/header-check-neon" \
  > "$cert_dir/neon-alias-build.log" 2>&1
nice -n 10 "$cert_dir/header-check-neon" > "$cert_dir/neon-alias.log"

nice -n 10 clang++ -std=c++17 -O1 -g -DNEON_DISPATCH_ALIASES \
  -fsanitize=signed-integer-overflow -fno-sanitize-recover=all \
  "$cert_dir/header-check.cpp" -o "$cert_dir/header-check-neon-ubsan" \
  > "$cert_dir/neon-ubsan-build.log" 2>&1
if nice -n 10 "$cert_dir/header-check-neon-ubsan" witness \
   > "$cert_dir/neon-signed-overflow.log" 2>&1; then
  echo "ERROR: the signed Sum overflow diagnostic was expected" >&2
  exit 1
fi
echo "PASS: scalar and disclosed NEON checks; expected native build/overflow diagnostics"
