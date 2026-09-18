#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if [[ -f ../env.sh ]]; then source ../env.sh; fi
export LEAN_NUM_THREADS=8
nice -n 10 taskset -c 88-95 lake build
python3 halftime_audit.py
nice -n 10 taskset -c 88-95 lake env lean HalftimeAudit.lean > HalftimeAudit.txt
python3 halftime_audit.py --check
