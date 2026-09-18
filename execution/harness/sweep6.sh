#!/usr/bin/env bash
cd "$(dirname "$0")"
L=logs/sweep6.jsonl
run() { echo "### $* (start $(date -Is))" >> $L; nice -n 10 "$@" >> $L 2>&1; echo "### done $(date -Is)" >> $L; }
run ./run_native B 2 30 48 main 1500
run ./run_native B 1 30 48 main 1500
touch logs/ALL6_DONE
