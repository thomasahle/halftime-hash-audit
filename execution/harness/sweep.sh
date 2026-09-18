#!/usr/bin/env bash
# Phase 1 (native dispatch, 2^34, per-b) already completed: logs/phase1.jsonl.
cd "$(dirname "$0")"
L=logs/sweep.jsonl
run() { echo "### $* (start $(date -Is))" >> $L; nice -n 10 "$@" >> $L 2>&1; echo "### done $(date -Is)" >> $L; }

# Phase 2: (B) overlap search, 2^30 keys, Style64 (b=1) and Style128 (b=2), scalar dispatch
for b in 1 2; do run ./run_scalar B $b 30 48 short 900; done
for b in 1 2; do run ./run_scalar B $b 30 48 main 2400; done
touch logs/PHASE2_DONE

# Phase 3: (A) headline, scalar dispatch, 2^36
for b in 1 2 4 8; do run ./run_scalar A $b 36 48 pair2 2600; done
touch logs/PHASE3_DONE

# Phase 4: extras
for b in 1 2 4 8; do run ./run_scalar cond $b 28 48 zero 600; done
for b in 1 2 4 8; do run ./run_scalar cond $b 28 48 nonzero 600; done
for b in 1 2; do run ./run_native B $b 30 48 main 1200; done
for b in 1 2; do run ./run_scalar B $b 28 48 var 1200; done
for b in 1 2 4 8; do run ./run_scalar A $b 32 48 all 600; done
touch logs/ALL_DONE
