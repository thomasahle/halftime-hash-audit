#!/usr/bin/env bash
cd "$(dirname "$0")"
L=logs/sweep5.jsonl
run() { echo "### $* (start $(date -Is))" >> $L; nice -n 10 "$@" >> $L 2>&1; echo "### done $(date -Is)" >> $L; }
for i in 1 2 3; do run ./run_scalar A 4 36 48 pair2 540; touch logs/A4_CHUNK_$i; done
touch logs/A4_DONE
for b in 1 2; do run ./run_native B $b 30 48 main 1500; done
touch logs/ALL5_DONE
