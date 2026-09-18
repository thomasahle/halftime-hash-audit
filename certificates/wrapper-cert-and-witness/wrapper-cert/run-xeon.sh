#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
cert_dir=review-support/wrapper-cert
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1

uname -a > "$cert_dir/xeon-environment.log"
clang++ --version >> "$cert_dir/xeon-environment.log"
sha256sum halftime-current.hpp halftime-current.tex >> "$cert_dir/xeon-environment.log"
nice -n 10 python3 "$cert_dir/certificates.py" > "$cert_dir/certificates.log"

nice -n 10 clang++ -std=c++17 -O2 -fwrapv -march=native \
  "$cert_dir/header-check.cpp" -o "$cert_dir/header-check-avx512" \
  > "$cert_dir/xeon-avx512-build.log" 2>&1
nice -n 10 "$cert_dir/header-check-avx512" > "$cert_dir/xeon-avx512.log"

nice -n 10 clang++ -std=c++17 -O2 -fwrapv -msse2 -mno-avx \
  "$cert_dir/header-check.cpp" -o "$cert_dir/header-check-sse2" \
  > "$cert_dir/xeon-sse2-build.log" 2>&1
nice -n 10 "$cert_dir/header-check-sse2" > "$cert_dir/xeon-sse2.log"

nice -n 10 clang++ -std=c++17 -O1 -g -fwrapv \
  -fsanitize=address,undefined -fno-sanitize-recover=all \
  "$cert_dir/layout-check.cpp" -o "$cert_dir/layout-check" \
  > "$cert_dir/xeon-layout-build.log" 2>&1
nice -n 10 "$cert_dir/layout-check" layout > "$cert_dir/layout.log"

if nice -n 10 "$cert_dir/layout-check" table > "$cert_dir/table-ubsan.log" 2>&1; then
  echo "ERROR: table-bound diagnostic was expected" >&2
  exit 1
fi
if nice -n 10 "$cert_dir/layout-check" boundary > "$cert_dir/boundary-asan.log" 2>&1; then
  echo "ERROR: stack-sentinel diagnostic was expected" >&2
  exit 1
fi
echo "PASS: exact certificates, native checks, layout, and expected diagnostics"
