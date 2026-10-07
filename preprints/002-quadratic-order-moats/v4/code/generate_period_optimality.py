#!/usr/bin/env python3
from collections import deque
from math import isqrt
import json
from pathlib import Path

F8=tuple((a,b) for a in (-1,0,1) for b in (-1,0,1) if (a,b)!=(0,0))

def prime_factors(n):
    out=[]; p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0: n//=p
        p=3 if p==2 else p+2
    if n>1: out.append(n)
    return out

def squarefree(n):
    fs=prime_factors(n)
    return n==__import__('math').prod(fs)

def sumsq_prime(p):
    for a in range(1,isqrt(p)+1):
        b2=p-a*a
        b=isqrt(b2)
        if b and b*b==b2:
            return (a,b)
    raise AssertionError(p)

def maximal_generators(q):
    gs=[]
    for p in prime_factors(q):
        if p==2:
            gs.append((1,1))
        elif p%4==1:
            a,b=sumsq_prime(p)
            gs += [(a,b),(a,-b)]
        else:
            gs.append((p,0))
    return tuple(gs)

def divisible(z,alpha):
    x,y=z; a,b=alpha; D=a*a+b*b
    return (a*x+b*y)%D==0 and (-b*x+a*y)%D==0

def allowed_residues(q,gs):
    return {(x,y) for x in range(q) for y in range(q)
            if all(not divisible((x,y),g) for g in gs)}

def edge(r,d,q):
    x=r[0]+d[0]; y=r[1]+d[1]
    s=(x%q,y%q)
    k=((x-s[0])//q,(y-s[1])//q)
    return s,k

def path_steps(parent,v):
    rev=[]
    while parent[v] is not None:
        u,d=parent[v]
        rev.append(d); v=u
    return list(reversed(rev))

def failure_witness(q):
    gs=maximal_generators(q)
    A=allowed_residues(q,gs)
    h={}
    for root in sorted(A):
        if root in h: continue
        h[root]=(0,0)
        parent={root:None}
        todo=deque([root])
        while todo:
            r=todo.popleft()
            for d in F8:
                s,k=edge(r,d,q)
                if s not in A: continue
                want=(h[r][0]+k[0],h[r][1]+k[1])
                if s not in h:
                    h[s]=want; parent[s]=(r,d); todo.append(s)
                elif h[s]!=want:
                    pr=path_steps(parent,r)
                    ps=path_steps(parent,s)
                    walk=pr+[d]+[(-a,-b) for a,b in reversed(ps)]
                    dx=sum(a for a,b in walk);dy=sum(b for a,b in walk)
                    assert dx%q==0 and dy%q==0
                    voltage=(dx//q,dy//q)
                    assert voltage!=(0,0)
                    return dict(
                        q=q,
                        rational_primes=prime_factors(q),
                        generators=[list(g) for g in gs],
                        root=list(root),
                        steps=[list(d) for d in walk],
                        voltage=list(voltage),
                        allowed_residues=len(A))
    return None

cases=[]
# q=1: full lattice has the one-step voltage witness.
cases.append(dict(q=1,rational_primes=[],generators=[],root=[0,0],
                  steps=[[1,0]],voltage=[1,0],allowed_residues=1))
for q in range(2,130):
    if not squarefree(q): continue
    w=failure_witness(q)
    if w is None:
        raise RuntimeError(f'unexpected finite maximal sieve at q={q}')
    cases.append(w)

out={
 'schema':'mxym-math-002-v4-gaussian-f8-period-optimality-1',
 'scope':'Exact nonzero-voltage witnesses for every squarefree radical q<130; positive q=130 certificate is inherited and checked separately.',
 'step_set':'F8',
 'failed_radicals':cases,
 'positive_period':130,
 'positive_generators':[[1,1],[2,1],[2,-1],[3,2],[3,-2]],
 'positive_certificate':'../v3/certificates_v3/gaussian_eight_steps_principal.json'
}
(Path(__file__).resolve().parent/'period_optimality.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('generated',len(cases),'failed radicals')
print('max witness length',max(len(c['steps']) for c in cases))
print('total witness steps',sum(len(c['steps']) for c in cases))
