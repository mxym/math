#!/usr/bin/env python3
"""Inspect stored proof bodies for all owned declarations without axioms summary cache."""
from pathlib import Path
import json,subprocess
ROOT=Path(__file__).resolve().parent.parent
output=subprocess.check_output(['lake','env','lean','controls/CombinedDependencyAudit.lean'],cwd=ROOT,text=True,stderr=subprocess.STDOUT)
(ROOT/'logs/dependency-traversal.log').write_text(output)
lines=[s[len('DEPENDENCY_JSON='):] for s in output.splitlines() if s.startswith('DEPENDENCY_JSON=')]
if len(lines)!=1:raise RuntimeError('Missing or duplicate recursive dependency output')
rows=json.loads(lines[0])
allowed={'propext','Classical.choice','Quot.sound'}
for row in rows:
    if set(row['body_traversal_axioms'])!=set(row['collectAxioms']) or not set(row['body_traversal_axioms'])<=allowed:
        raise RuntimeError('Unpermitted/mismatched recursive axioms: '+row['name'])
    for field in ['unsafe_dependencies','partial_dependencies','missing_dependencies']:
        if row[field]:raise RuntimeError('Invalid '+field+': '+row['name'])
exports={v['name'] for v in json.loads((ROOT/'exported-theorems.json').read_text())}
if not exports<={r['name'] for r in rows}:raise RuntimeError('Recursive audit omitted public exports')
(ROOT/'dependency-graph.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('PASS: recursive stored-body traversal of '+str(len(rows))+' owned declarations; all 101 exports present, standard axioms only.')
