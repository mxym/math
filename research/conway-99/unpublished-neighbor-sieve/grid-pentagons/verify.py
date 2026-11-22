"""Verify the obstruction on nine exceptional roots. Uses Python, NumPy and C++17."""

import ctypes
import gzip
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from covered_spread import PAIRS, row_system, verify_permutations

EDGES = list(combinations(range(5), 2))
DIST = np.array([min(b-a, 5+a-b) for a,b in EDGES])
LABELS = np.array(EDGES)
LINES = [(0,1,2),(3,4,5),(6,7,8),(0,3,6),(1,4,7),(2,5,8)]


def adjacent(p, q):
    return p != q and (p//3 == q//3 or p%3 == q%3)


NEAR = [[q for q in range(9) if adjacent(p,q)] for p in range(9)]
FAR = [[q for q in range(9) if p != q and not adjacent(p,q)] for p in range(9)]
MASKS = np.array([[sum(((g>>q)&1)<<j for j,q in enumerate(far)) for far in FAR]
                  for g in range(512)])


def read_evidence(name):
    with gzip.open(HERE / name, 'rt') as f:
        return json.load(f)


def local_pentagon():
    code = 733007422869
    arcs = []
    for k,(a,b) in enumerate(PAIRS):
        value = (code>>(2*k)) & 3
        if value:
            arcs.append((a,b) if value==1 else (b,a))
    assert set(arcs) == ({(a,(a+d)%5) for a in range(5) for d in (1,2)}
                         | {(p,a) for p in (5,6) for a in range(5)})
    group = [j for j,(a,b) in enumerate(arcs) if a==5]
    assert [arcs[j][1] for j in group] == list(range(5))
    sides = tuple(int(d==1) for d in DIST)
    proofs = read_evidence('pentagon.json.gz')
    assert ''.join(map(str,sides)) not in proofs
    assert verify_permutations(row_system(arcs),group,[proofs[k] for k in sorted(proofs)],
                               omit=sides) == 21


def transfers(code):
    free = list(map(int,f'{code%10000:04d}'))
    moves = np.zeros((9,9,5),dtype=int)
    def edge(p,q,x):
        moves[p,q] = x
        moves[q,p] = np.argsort(x)
    for k,(a,b,c) in enumerate(LINES):
        digits = (0,0) if k<4 else free[2*(k-4):2*(k-4)+2]
        x,y = [(u + (1 if u<5 else -1)*np.arange(5))%5 for u in digits]
        turn = -1 if (code//10000)&(1<<k) else 1
        edge(a,b,x)
        edge(a,c,y)
        edge(b,c,y[(np.argsort(x)+turn)%5])
    return moves, all(v<5 for v in free)


def unpack(entries, width):
    out = np.zeros(width,dtype=np.int64)
    for j,v in entries:
        assert 0<=j<width and 0<abs(v)<=10**8 and out[j]==0
        out[j]=v
    return out


def balances(words, column):
    e=words[:,column]
    return np.array([(e==j).astype(np.int8)-(e==group[0])
                     for distance in (2,1)
                     for group in [np.flatnonzero(DIST==distance)] for j in group[1:]])


def local_rejections(s, by_mask, proofs):
    us = [unpack(weights,32) for root,weights in proofs if root==s]
    rejected = set()
    for mask,w in by_mask.items():
        if len(set(w[:,0]))<5:
            rejected.add(mask)
        elif us:
            coeff = np.vstack([balances(w,j) for j in range(1,5)])
            vals = np.array(us) @ coeff
            maxima = sum(vals[:,w[:,0]==i].max(axis=1) for i in range(5))
            if np.any(maxima<0):
                rejected.add(mask)
    return rejected


def coefficients(keys, moves, cyclic, s, words):
    n=len(words)
    mat=np.zeros((len(keys),n),dtype=np.int8)
    i=words[:,0]
    contacts={p:moves[s,p,i][:,None] for p in NEAR[s]}
    for pos,q in enumerate(FAR[s]):
        e=words[:,pos+1]
        contacts[q]=LABELS[e]
        if cyclic:
            key=('sides',q)
            if key in keys: mat[keys[key]] += DIST[e]==1
        else:
            for j in range(10):
                key=('four',q,j)
                if key in keys: mat[keys[key]] += e==j
            for distance in (1,2):
                first,*rest=np.flatnonzero(DIST==distance)
                for j in rest:
                    key=('balance',s,q,int(j))
                    if key in keys:
                        mat[keys[key]] += (e==j).astype(np.int8)-(e==first)
        p0,p1=sorted((s,q))
        for j in range(5):
            for h in range(1 if cyclic else 5):
                key=('pair',p0,p1,h,j)
                if key not in keys:continue
                for other in contacts[q].T:
                    lo,hi=(i,other) if s<q else (other,i)
                    use=(hi-lo)%5==j if cyclic else ((lo==h)&(hi==j))
                    mat[keys[key]] += use.astype(np.int8)*(1 if s<q else -1)
    for p,q in combinations(sorted(contacts),2):
        if not adjacent(p,q):continue
        for j in range(1 if cyclic else 5):
            key=('cap',p,q,j)
            if key not in keys:continue
            for label in contacts[p].T:
                for other in contacts[q].T:
                    hit=moves[p,q,label]==other
                    if not cyclic: hit &= label==j
                    mat[keys[key]] += hit
    return mat


def global_rejections(moves, cyclic, viable, candidates, proofs):
    tags=sorted({tuple(k) for w in proofs for k,_ in w})
    keys={k:i for i,k in enumerate(tags)}
    rhs={'sides':4,'four':4,'balance':0,'pair':0,'cap':2}
    b=np.array([rhs[k[0]] for k in tags],dtype=np.int64)
    u=np.array([unpack([(keys[tuple(k)],v) for k,v in w],len(tags)) for w in proofs])
    bounds=np.zeros((len(proofs),len(viable)),dtype=np.int64)
    for s in range(9):
        masks=np.unique(MASKS[viable,s])
        items=[candidates(s,int(mask)) for mask in masks]
        if cyclic: items=[w[w[:,0]==0] for w in items]
        w=np.concatenate(items)
        assert len(w)
        score=u @ coefficients(keys,moves,cyclic,s,w)
        start=0
        for mask,part in zip(masks,items):
            values=score[:,start:start+len(part)]
            start+=len(part)
            bound=sum(values[:,part[:,0]==i].max(axis=1) for i in range(1 if cyclic else 5))
            bounds[:,MASKS[viable,s]==mask] += 2*bound[:,None]
    assert np.all(np.any((u@b)[:,None]>bounds,axis=0))


def verify_chart(lib, code, proof, buf):
    moves,cyclic=transfers(code)
    viable=np.arange(512)
    cache={}
    def candidates(s,mask):
        if (s,mask) not in cache:
            n=lib.local_words(code,s,mask,buf.ctypes.data_as(ctypes.POINTER(ctypes.c_int)))
            assert 0<=n<=50000
            cache[s,mask]=buf[:n].copy()
        return cache[s,mask]
    for s in range(9):
        items={int(h):candidates(s,int(h)) for h in np.unique(MASKS[viable,s])}
        bad=local_rejections(s,items,proof['l'])
        viable=viable[~np.isin(MASKS[viable,s],list(bad))]
        if not len(viable):return
    assert proof['g']
    global_rejections(moves,cyclic,viable,candidates,proof['g'])


def main():
    local_pentagon()
    proofs=read_evidence('charts.json.gz')
    with TemporaryDirectory() as tmp:
        libpath=Path(tmp)/'charts.so'
        subprocess.run(['c++','-O3','-std=c++17','-fPIC','-shared',str(HERE/'charts.cpp'),
                        '-o',str(libpath)],check=True)
        lib=ctypes.CDLL(str(libpath))
        keys=np.empty(640000,dtype=np.int32)
        sizes=keys.copy()
        ptr=ctypes.POINTER(ctypes.c_int)
        n=lib.list_charts(keys.ctypes.data_as(ptr),sizes.ctypes.data_as(ptr))
        assert n==1364 and sizes[:n].sum()==640000
        assert set(keys[:n])==set(map(int,proofs))
        buf=np.empty((50000,5),dtype=np.int32)
        for code in keys[:n]:
            verify_chart(lib,int(code),proofs[str(code)],buf)
    print('Verified the pentagon and all 1,364 transport representatives, with all 512 orientations each.')


if __name__=='__main__':
    main()
