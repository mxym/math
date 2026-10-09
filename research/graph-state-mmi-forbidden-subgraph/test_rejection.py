#!/usr/bin/env python3
"""Negative tests: both independently implemented checkers must reject mutations."""
from copy import deepcopy
import json
from pathlib import Path
import check_certificate as bit
import verify_independent as independent

root=Path(__file__).resolve().parent
cert=json.loads((root/'certificate.json').read_text())

def main():
    changes=[]
    def add(name, change):
        c=deepcopy(cert);change(c);changes.append((name,c))
    add('missing extension',lambda c:c['extensions'].pop())
    add('duplicate extension',lambda c:c['extensions'].append(deepcopy(c['extensions'][0])))
    add('invalid LC vertex',lambda c:c['extensions'][0]['lc'].append(99))
    add('wrong representative',lambda c:c['representatives']['2'].__setitem__(0,0))
    add('nonbijective relabeling',lambda c:c['extensions'][0].__setitem__('order',[0,0]))
    j=next(i for i,w in enumerate(cert['extensions']) if w['kind']=='claw')
    add('repeated claw leaf',lambda c:c['extensions'][j].__setitem__('claw',[0,1,1,2]))
    add('missing closed-orbit state',lambda c:c['closed_claw_free_orbits']['5'].pop())
    add('loop in closed set',lambda c:c['closed_claw_free_orbits']['6'][0].__setitem__(0,c['closed_claw_free_orbits']['6'][0][0]|1))
    passed=[]
    for name,c in changes:
        for checker,fn in [('bitmask',bit.verify),('edge-set',lambda d:independent.verify(d,False))]:
            try:fn(c)
            except (ValueError,RuntimeError,KeyError,TypeError,IndexError):passed.append([name,checker])
            else:raise RuntimeError(f'Mutation accepted: {name}, {checker}')
    print(json.dumps({'status':'PASS','mutations':len(changes),'rejections':len(passed),'tests':passed},indent=2))

if __name__=='__main__':main()
