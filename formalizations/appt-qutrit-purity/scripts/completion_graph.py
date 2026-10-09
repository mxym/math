#!/usr/bin/env python3
"""Derive and validate the local module DAG directly from all APPT source imports."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parent.parent
graph={}
for path in sorted([root/'APPT.lean',*(root/'APPT').rglob('*.lean')]):
    name='.'.join(path.relative_to(root).with_suffix('').parts)
    deps=[]
    for line in path.read_text().splitlines():
        if line.startswith('import '):deps += [m for m in line[7:].split() if m=='APPT' or m.startswith('APPT.')]
    graph[name]=sorted(set(deps))
for name,deps in graph.items():
    for d in deps:
        if d not in graph:raise RuntimeError('Missing import '+d+' for '+name)
def closure(roots):
    out={}
    def visit(m,active):
        if m in active:raise RuntimeError('Cyclic import '+m)
        if m in out:return
        for d in graph[m]:visit(d,active|{m})
        out[m]=graph[m]
    for m in roots:visit(m,set())
    return dict(sorted(out.items()))
for D in [9,12,15,18,21,24]:
    result={'modules':closure([f'APPT.Finite{D}Bound'])}
    (root/f'generated-Dimension{D}.json').write_text(json.dumps(result,indent=2)+'\n')
(root/'generated-UniformBuild.json').write_text(json.dumps({'modules':closure(['APPT.Quantum.LargeMaximum','APPT.Quantum.SpectralNecessity','APPT.Quantum.SpectralMoment'])},indent=2)+'\n')
(root/'generated-All.json').write_text(json.dumps({'modules':closure(sorted(graph))},indent=2)+'\n')
print('Checked',len(graph),'local modules')
