#!/usr/bin/env python3
"""Generate/check the explicit #check and #print axioms audit for this extension."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
imports = re.findall(r'^import (ProvenHashes\.Halftime\.\w+)$',
                     (root / 'ProvenHashes.lean').read_text(), re.M)
names = []
for module in imports:
    path = root / (module.replace('.', '/') + '.lean')
    source = path.read_text()
    namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
    for name in re.findall(r'^(?:theorem|lemma) (\w+)', source, re.M):
        names.append(namespace + '.' + name)
audit = 'import ProvenHashes\n\n' + '\n'.join(
    f'#check @{name}\n#print axioms {name}' for name in names) + '\n'
if '--check' not in sys.argv:
    (root / 'HalftimeAudit.lean').write_text(audit)
    print(f'Generated audit for {len(names)} Halftime proof declarations.')
    raise SystemExit

assert (root / 'HalftimeAudit.lean').read_text() == audit, 'Audit is stale'
for path in (root / 'ProvenHashes').rglob('*.lean'):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b', source), path
    assert not re.search(r'^\s*(axiom|unsafe)\b', source, re.M), path
log = (root / 'HalftimeAudit.txt').read_text()
rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
empty = re.findall(r"'([^']+)' does not depend on any axioms", log)
assert set(names) == {name for name, _ in rows} | set(empty), 'Missing axiom output'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in rows:
    found = {a.strip() for a in axioms.split(',') if a.strip()}
    assert found <= allowed, (name, found)
assert not re.search(r'error:|sorryAx|Lean.ofReduceBool', log)
print(f'Halftime axiom audit passed: {len(names)} proof declarations; only standard Lean axioms.')
