#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
CXX=${CXX:-g++}
COMMON="-std=c++17 -O3 -fwrapv -fno-strict-aliasing -Wall"
# scalar dispatch build: header specializes V1..V4 to VjScalar
$CXX $COMMON -march=native -DSCALAR_DISPATCH -c hh_api.cpp -o hh_api_scalar.o 2> build_scalar.log || { cat build_scalar.log; exit 1; }
# native dispatch build: header takes its own AVX-512 branch on this machine
$CXX $COMMON -march=native -c hh_api.cpp -o hh_api_native.o 2> build_native.log || { cat build_native.log; exit 1; }
$CXX $COMMON -march=native -fopenmp run.cpp hh_api_scalar.o -o run_scalar
$CXX $COMMON -march=native -fopenmp run.cpp hh_api_native.o -o run_native
echo "built run_scalar run_native"
