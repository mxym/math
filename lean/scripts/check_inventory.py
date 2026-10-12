#!/usr/bin/env python3
"""Match compiler-known public theorem declarations to the full source inventory."""
from pathlib import Path
import json,subprocess
ROOT=Path(__file__).resolve().parent.parent
output=subprocess.check_output(['lake','env','lean','controls/IndependentAudit.lean'],cwd=ROOT,text=True,stderr=subprocess.STDOUT)
(ROOT/'logs/compiler-inventory.log').write_text(output)
rows=[json.loads(line) for line in output.splitlines() if line.startswith('{')]
if not rows:raise RuntimeError('Missing compiler declaration inventory')
exports={r['name'] for r in rows if r['kind']=='theorem' and not r['private'] and not r['internal_detail'] and not r['equation'] and not r['name'].endswith(('.congr_simp','.eq_def'))}
expected=json.loads((ROOT/'exported-theorems.json').read_text())
if len(expected)!=101 or len({r['name'] for r in expected})!=101 or exports!={r['name'] for r in expected}:
    raise RuntimeError('Compiler/source export inventory mismatch')
if any(r['kind'] in {'axiom','opaque'} or ((r['unsafe'] or r['partial']) and not r['internal_detail']) for r in rows):
    raise RuntimeError('Unpermitted owned declaration')
counts={kind:sum(r['kind']==kind for r in rows) for kind in {r['kind'] for r in rows}}
(ROOT/'declaration-inventory.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('PASS: exact 101 public exports; owned compiler declaration counts = '+json.dumps(counts,sort_keys=True))
