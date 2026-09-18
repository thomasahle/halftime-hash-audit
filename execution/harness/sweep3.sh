#!/usr/bin/env bash
cd "$(dirname "$0")"
L=logs/sweep3.jsonl
run() { echo "### $* (start $(date -Is))" >> $L; nice -n 10 "$@" >> $L 2>&1; echo "### done $(date -Is) rc=$?" >> $L; }
# A b=8 in resumable chunks: each chunk is an independent run with its own
# getrandom seed, so their trials and hits add.
for i in 1 2 3 4 5 6 7 8 9 10 11 12; do run ./run_scalar A 8 36 48 pair2 540; touch logs/A8_CHUNK_$i; done
touch logs/A8_DONE
run ./run_scalar cond 1 28 48 zero 600
run ./run_scalar cond 8 28 48 zero 600
for b in 1 2 4 8; do run ./run_scalar cond $b 28 48 nonzero 600; done
touch logs/COND_DONE
for b in 1 2 4 8; do run ./run_scalar A $b 32 48 all 600; done
for b in 1 2; do run ./run_native B $b 30 48 main 1500; done
touch logs/ALL3_DONE
