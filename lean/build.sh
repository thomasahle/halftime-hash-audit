#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if [[ -f ../env.sh ]]; then
  source ../env.sh
fi
export LEAN_NUM_THREADS=8
nice -n 10 taskset -c 88-95 lake build
nice -n 10 taskset -c 88-95 lake env lean Audit.lean > Audit.txt
nice -n 10 taskset -c 88-95 lake env lean FullAudit.lean > FullAudit.txt
python3 - <<'PY'
from pathlib import Path
import re
for p in Path('ProvenHashes').glob('*.lean'):
    s=p.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b',s), p
    assert not re.search(r'^\s*(axiom|unsafe)\b',s,re.M), p
s=Path('FullAudit.txt').read_text()
rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s)
expected=set(re.findall(r'#print axioms (\S+)', Path('FullAudit.lean').read_text()))
assert {name for name, _ in rows} == expected, 'Missing axiom output'
allowed={'propext','Classical.choice','Quot.sound'}
for name, axioms in rows:
    found={a.strip() for a in axioms.split(',') if a.strip()}
    assert found <= allowed, (name,found)
assert not re.search(r'error:|sorryAx|Lean.ofReduceBool',s)
print(f'Build and axiom audit passed ({len(rows)} proof declarations with axiom lists).')
PY
