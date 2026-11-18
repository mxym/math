"""Exact verification. Python 3 + NumPy, plus g++ and GMP for base_recount.cpp.
Usage: python verify.py /path/to/c89_stepgraphon_D20.json.gz
"""
from fractions import Fraction
from itertools import product, combinations
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,tempfile
import numpy as np
BASE=Fraction(27220838459434583306277336063848530765605851167,903180180540490237232196590042258640992206848000)
DELTA=Fraction(-729010652335333284981507141875700526289,1505300300900817062053660983403764401653678080000)
BOUND=Fraction(17013023763767619940673353171840153525115959621,564487612837806398270122868776411650620129280000)
if not __debug__:
    raise SystemExit("Certificate assertions require ordinary Python (no -O or -OO).")
HERE=Path(__file__).resolve().parent
def change(R,D,records):
    n=len(R); assert np.array_equal(R,R.T) and np.all(np.diag(R)==0) and R.min()>=0 and R.max()<=D
    assert D**3 * 5 < 2**63 # Every 5-entry partial sum fits in signed int64.
    seen=set(); delta=0; H=[]
    for i,j,k,a,b,c in records:
        assert 0<=i<j<k<n
        P=[(i,j),(i,k),(j,k)]; V=[a,b,c]; r=[int(R[x,y]) for x,y in P]
        for edge,amp,red in zip(P,V,r):
            assert edge not in seen and 0<abs(amp)<=min(red,D-red);seen.add(edge)
        v,w,z=(R[h].astype(np.int64) for h in (i,j,k))
        h=v*w*z-(D-v)*(D-w)*(D-z) # each entry is exact; chunk before summing
        if n%5==0: h=sum(map(int,h.reshape(-1,5).sum(axis=1)))
        else:h=sum(map(int,h))
        cubic=24*h*a*b*c
        quart=6*D**2*sum(x**4 for x in V)+12*D*sum((D-r[t])*V[(t+1)%3]**2*V[(t+2)%3]**2 for t in range(3))
        H.append(cubic+quart)
        delta+=cubic+quart
    return Fraction(delta,n**4*D**6),H
def brute(A,D):
    n=len(A); s=0
    for x in product(range(n),repeat=4):
        p=q=1
        for a,b in combinations(range(4),2):
            e=int(A[x[a],x[b]]);p*=e;q*=D-e
        s+=p+q
    return Fraction(s,n**4*D**6)
def small_check():
    D=16; u=np.random.default_rng(603).integers(3,13,size=(5,5)); u=np.triu(u,1);u=u+u.T
    ts=[(0,1,2,-2,1,3),(2,3,4,1,3,-2)]
    sig=list(product((-1,1),repeat=2)); vs=list(product(range(5),sig))
    A=np.array([[u[i,j] for j,_ in vs] for i,_ in vs])
    for t,(i,j,k,a,b,c) in enumerate(ts):
        amp={(i,j):a,(i,k):b,(j,k):c}
        for v,(v0,s) in enumerate(vs):
            for w,(w0,z) in enumerate(vs):
                A[v,w]+=amp.get(tuple(sorted((v0,w0))),0)*s[t]*z[t]
    den,H=change(u,D,ts);assert den==brute(A,D)-brute(u,D)
def k4_support(W,D):
    N=len(W); G=(W>0)&(W<D); adj=[sum(1<<int(j) for j in np.flatnonzero(G[i]) if j>i) for i in range(N)]
    triangles=fours=0
    for i,ne in enumerate(adj):
        m=ne
        while m:
            u=m&-m; m^=u;j=u.bit_length()-1; q=ne&adj[j];triangles+=q.bit_count()
            while q:
                u=q&-q;q^=u;fours+=(q&adj[u.bit_length()-1]).bit_count()
    return int(G.sum())//2,triangles,fours
def main():
    ap=argparse.ArgumentParser();ap.add_argument('base',type=Path);ap.add_argument('--skip-base-recount',action='store_true');args=ap.parse_args()
    assert BOUND-BASE==DELTA and DELTA<0
    # Bind the public-facing decimals' exact sources, rather than only printing them.
    note=''.join((HERE/'README.md').read_text(encoding='utf-8').split())
    assert f'B={BASE.numerator}/{BASE.denominator}' in note
    assert f'{DELTA.numerator}/{DELTA.denominator}' in note
    assert rf'c_4\le\frac{{{BOUND.numerator}}}{{{BOUND.denominator}}}' in note
    small_check()
    raw=args.base.read_bytes();assert hashlib.sha256(raw).hexdigest()=='82c28f7761f8392df6ed1728b5eefdc4ef388b266fc2beb1a2f0a54f7dd2631a'
    d=json.loads(gzip.decompress(raw));D=d['edge_probability_denominator'];assert D==2**20 and d['block_weights']==[1]*3840
    R=np.asarray(d['red_probability_numerators'],dtype=np.int64);assert R.shape==(3840,3840)
    if not args.skip_base_recount:
        with tempfile.TemporaryDirectory() as td:
            td=Path(td);R.astype('<i4').tofile(td/'base.i32')
            subprocess.run(['g++','-O3','-std=c++17',str(HERE/'base_recount.cpp'),'-lgmpxx','-lgmp','-o',str(td/'recount')],check=True)
            rec=Fraction(subprocess.check_output([str(td/'recount'),str(td/'base.i32')],text=True).strip());assert rec==BASE
            print('Independently recounted base:',rec)
    print('fractional support (#edges, #triangles, #K4):',k4_support(R,D))
    data=(HERE/'triangles.tsv.gz').read_bytes();assert hashlib.sha256(data).hexdigest()=='f5be0d010110b6ecaf2eb618efb1909197c2c6eea11fd64c6288f4f263072411'
    ts=[tuple(map(int,l.split())) for l in gzip.decompress(data).splitlines()]
    # Each color is a vertex-disjoint collection of triangles.
    used=[set() for _ in range(len(R))]; colors=[]
    for i,j,k,*_ in ts:
        forbidden=used[i]|used[j]|used[k]; c=next(a for a in range(33) if a not in forbidden)
        for z in (i,j,k):used[z].add(c)
        colors.append(c)
    assert max(colors)+1==23
    print('triangle labels:',max(colors)+1,'; fiber states: 64; total step classes:',64*len(R))
    dlt,H=change(R,D,ts);assert len(H)==8320 and max(H)<0;end=BASE+dlt
    assert dlt==DELTA and end==BOUND
    print('triangle count:',len(ts),'\ndelta:',dlt,'\nresult:',end,'\napproximation:',format(float(end),'.17g'))
if __name__=='__main__':main()
