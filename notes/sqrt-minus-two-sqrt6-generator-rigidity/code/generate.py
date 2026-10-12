#!/usr/bin/env python3
"""Nontrusted deterministic certificate discovery; NOT used by check.py."""
from collections import deque
from pathlib import Path
import json

Q=1122
F=((-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
   (0,-1),(0,1),(1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1))
P=((0,1),(1,1),(1,-1),(3,1),(3,-1),(3,2),(3,-2))
REV=tuple(F.index((-a,-b)) for a,b in F)


def norm(z):
    a,b=z;return a*a+2*b*b


def divides(g,z):
    a,b=g;c,d=z;n=norm(g)
    return (a*c+2*b*d)%n==0 and (a*d-b*c)%n==0


def path(parents,v):
    seq=[]
    while parents[v] is not None:
        v,j=parents[v];seq.append(j)
    return seq[::-1]


def discover(index,square=False):
    gens=[g for j,g in enumerate(P) if j!=index]
    if square:gens.append((-2,0))
    def allowed(v):return not any(divides(g,v) for g in gens)
    marked=set()
    for a in range(Q):
        for b in range(Q):
            root=a,b
            if root in marked or not allowed(root):continue
            lifted={root:root};parent={root:None};queue=deque([root]);marked.add(root)
            while queue:
                residue=queue.popleft();x,y=lifted[residue]
                for j,(da,db) in enumerate(F):
                    p=x+da,y+db
                    z=p[0]%Q,p[1]%Q
                    if not allowed(p):continue
                    if z in lifted:
                        if lifted[z]!=p:
                            moves=path(parent,residue)+[j]+[
                                REV[k] for k in reversed(path(parent,z))]
                            return {'missing':index,'start':list(root),'steps':moves}
                    else:
                        lifted[z]=p;parent[z]=residue,j
                        queue.append(z);marked.add(z)
    raise ValueError('no nonzero-voltage obstruction found')

if __name__=='__main__':
    data={'prime_omissions':[discover(j) for j in range(7)],
          'ramified_square':discover(0,square=True)}
    dest=Path(__file__).with_name('obstructions.json')
    dest.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    print('generated',len(data['prime_omissions'])+1,'raw integer walks')
