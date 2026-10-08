#!/usr/bin/env python3
"""Discovery-only producer for the finite exceptional-prime overgraph."""
from collections import deque
from math import gcd
from pathlib import Path
import json
Q=1122
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),
   (2,-1),(2,0),(2,1))
G=((0,1),(1,1),(1,-1),(3,1),(3,-1),(3,2),(3,-2))
E={(s*a,s*b) for a,b in G for s in (-1,1)}
C=set(E);todo=deque(E)
while todo:
    a,b=todo.popleft()
    for da,db in F:
        z=(a+da,b+db)
        if z not in C and (z in E or gcd(z[0]**2+2*z[1]**2,Q)==1):
            C.add(z);todo.append(z)
out=Path(__file__).with_name('exceptional_closure.json')
out.write_text(json.dumps([list(z) for z in sorted(C)],separators=(',',':'))+'\n')
print('exceptional factor count',len(E),'closure points',len(C))
