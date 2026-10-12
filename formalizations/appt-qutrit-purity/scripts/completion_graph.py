#!/usr/bin/env python3
"""Derive and validate the local module DAG directly from all APPT source imports."""
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parent.parent
check='--check' in sys.argv
def emit(name,result):
    text=json.dumps(result,indent=2)+'\n'
    path=root/name
    if check:
        if not path.exists() or path.read_text()!=text:raise RuntimeError('Module graph mismatch: '+name)
    else:path.write_text(text)
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
    emit(f'generated-Dimension{D}.json',result)
emit('generated-UniformBuild.json',{'modules':closure(['APPT.Quantum.LargeMaximum','APPT.Quantum.SpectralNecessity','APPT.Quantum.SpectralMoment'])})
emit('generated-Probe24.json',{'modules':closure(['APPT.Finite24Sparse.Base04','APPT.Finite24Sparse.Leaf002','APPT.Finite24Sparse.Target'])})
emit('generated-All.json',{'modules':closure(sorted(graph))})
print('Checked',len(graph),'local modules')
