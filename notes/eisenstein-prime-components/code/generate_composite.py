#!/usr/bin/env python3
"""Producer for 36 composite-replacement voltage walks; checker is separate."""
from collections import deque
from itertools import product
from pathlib import Path
import gzip
import json

HERE=Path(__file__).resolve().parent
Q=546
STEPS=tuple((a,b) for a in (-1,0,1) for b in (-1,0,1) if a or b)
REV=tuple(STEPS.index((-a,-b)) for a,b in STEPS)


def flags(a,b):
    return ((a%2==0 and b%2==0), (a+b)%3==0,
            (a+4*b)%7==0, (a+2*b)%7==0,
            (a+9*b)%13==0, (a+3*b)%13==0)


def path(point, parents):
    result=[]
    while parents[point] is not None:
        point, idx=parents[point]
        result.append(idx)
    return result[::-1]


def produce(selected,j,extra):
    others=tuple(x for x in selected if x!=j)

    def allowed(z):
        a,b=z
        f=flags(a,b)
        if any(f[k] for k in others):
            return False
        if j==extra==1:
            return not (a%3==0 and b%3==0)
        return not (f[j] and f[extra])

    residues={(a,b) for a in range(Q) for b in range(Q) if allowed((a,b))}
    global_seen=set()
    for root in sorted(residues):
        if root in global_seen:
            continue
        lift={root:root}
        parent={root:None}
        queue=deque([root])
        while queue:
            v=queue.popleft()
            for idx,(da,db) in enumerate(STEPS):
                reached=(lift[v][0]+da,lift[v][1]+db)
                y=(reached[0]%Q,reached[1]%Q)
                if y not in residues:continue
                if y in lift:
                    if lift[y]!=reached:
                        seq=path(v,parent)+[idx]+[REV[t] for t in reversed(path(y,parent))]
                        return {'selected':list(selected),'slot':j,'extra':extra,
                                'base':list(root),'steps':seq}
                else:
                    lift[y]=reached
                    parent[y]=(v,idx)
                    queue.append(y)
        global_seen.update(lift)
    raise RuntimeError(f'no voltage for {selected},{j},{extra}')


if __name__=='__main__':
    data=[]
    for u,v in product((2,3),(4,5)):
        selected=(0,1,u,v)
        unused=tuple(sorted(set(range(6))-set(selected)))
        for j in selected:
            for extra in unused+((1,) if j==1 else ()):
                proof=produce(selected,j,extra)
                data.append(proof)
                print('proof',selected,j,extra,'length',len(proof['steps']),flush=True)
    raw=(json.dumps(data,separators=(',',':'),sort_keys=True)+'\n').encode('ascii')
    (HERE/'composite_replacement_cycles.json.gz').write_bytes(
        gzip.compress(raw,compresslevel=9,mtime=0))
    print('SAVED',len(data),'MAX_LENGTH',max(len(x['steps']) for x in data),
          'RAW_BYTES',len(raw),flush=True)
