#!/usr/bin/env python3
from collections import deque
from itertools import product,combinations
import json,math
from pathlib import Path

F8=tuple((a,b) for a in (-1,0,1) for b in (-1,0,1) if (a,b)!=(0,0))
PRIMES=((1,1),(2,1),(2,-1),(3,2),(3,-2))
Q=130

def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d,a*d+b*c)

def canon(z):
    a,b=z
    return min((a,b),(-b,a),(-a,-b),(b,-a))

def powg(z,n):
    r=(1,0)
    for _ in range(n):r=mul(r,z)
    return r

def divisors_130():
    out=set()
    for e2,e3,e4,e5,e6 in product(range(3),range(2),range(2),range(2),range(2)):
        z=(1,0)
        for p,e in zip(PRIMES,(e2,e3,e4,e5,e6)):
            z=mul(z,powg(p,e))
        out.add(canon(z))
    out.remove(canon((1,0)))
    assert len(out)==47
    return tuple(sorted(out))

def divisible(z,g):
    x,y=z;a,b=g;D=a*a+b*b
    return (a*x+b*y)%D==0 and (-b*x+a*y)%D==0

def allowed(z,gs):
    return all(not divisible(z,g) for g in gs)

def allowed_residues(gs):
    return {(x,y) for x in range(Q) for y in range(Q) if allowed((x,y),gs)}

def edge(r,d):
    x=r[0]+d[0];y=r[1]+d[1]
    s=(x%Q,y%Q)
    return s,((x-s[0])//Q,(y-s[1])//Q)

def path(parent,v):
    rev=[]
    while parent[v] is not None:
        u,d=parent[v];rev.append(d);v=u
    return list(reversed(rev))

def witness(gs):
    A=allowed_residues(gs);h={}
    for root in sorted(A):
        if root in h:continue
        h[root]=(0,0);parent={root:None};todo=deque([root])
        while todo:
            r=todo.popleft()
            for d in F8:
                s,k=edge(r,d)
                if s not in A:continue
                want=(h[r][0]+k[0],h[r][1]+k[1])
                if s not in h:
                    h[s]=want;parent[s]=(r,d);todo.append(s)
                elif h[s]!=want:
                    w=path(parent,r)+[d]+[(-a,-b) for a,b in reversed(path(parent,s))]
                    dx=sum(a for a,b in w);dy=sum(b for a,b in w)
                    assert dx%Q==0 and dy%Q==0 and (dx or dy)
                    return {'root':list(root),'steps':[list(d) for d in w],
                            'voltage':[dx//Q,dy//Q],'allowed_residues':len(A)}
    raise RuntimeError(f'unexpected successful list {gs}')

proper_subsets=[]
for k in range(5):
    for idxs in combinations(range(5),k):
        gs=tuple(PRIMES[i] for i in idxs)
        proper_subsets.append({'indices':list(idxs),'generators':[list(g) for g in gs],
                               'witness':witness(gs)})

divs=divisors_130()
replacement_cases=[]
for j,pi in enumerate(PRIMES):
    others=tuple(p for i,p in enumerate(PRIMES) if i!=j)
    for alpha in divs:
        if canon(alpha)==canon(pi):continue
        if not divisible(alpha,pi): # pi divides alpha iff alpha is in ideal (pi)
            continue
        gs=others+(alpha,)
        replacement_cases.append({
          'prime_index':j,'prime':list(pi),'replacement':list(alpha),
          'generators':[list(g) for g in gs],'witness':witness(gs)
        })

out={
 'schema':'mxym-math-002-v4-gaussian-f8-endpoint-rigidity-1',
 'period':130,
 'prime_generators':[list(p) for p in PRIMES],
 'all_nonunit_divisor_ideals':[list(a) for a in divs],
 'proper_prime_subset_failures':proper_subsets,
 'proper_subideal_replacement_failures':replacement_cases
}
target=Path(__file__).resolve().parent/'endpoint_rigidity.json'
target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print('divisor ideals',len(divs))
print('proper prime subsets',len(proper_subsets))
print('replacement cases',len(replacement_cases))
Ls=[len(x['witness']['steps']) for x in proper_subsets]+[len(x['witness']['steps']) for x in replacement_cases]
print('witnesses',len(Ls),'total steps',sum(Ls),'max length',max(Ls))
