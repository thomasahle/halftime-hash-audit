#!/usr/bin/env bash
cd "$(dirname "$0")"
L=logs/sweep4.jsonl
run() { echo "### $* (start $(date -Is))" >> $L; nice -n 10 "$@" >> $L 2>&1; echo "### done $(date -Is)" >> $L; }
run ./run_scalar cond 1 28 48 zero 500
run ./run_scalar cond 8 28 48 zero 500
for b in 1 2 4 8; do run ./run_scalar cond $b 28 48 nonzero 500; done
touch logs/COND_DONE
for b in 1 2 4 8; do run ./run_scalar A $b 32 48 all 500; done
touch logs/CTRL_DONE
for b in 1 2; do run ./run_native B $b 30 48 main 1500; done
touch logs/ALL4_DONE
