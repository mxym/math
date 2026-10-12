#!/usr/bin/env python3
"""Generate fixed exact certificates for the S_n three-subset atom/TV problem.

Degree range is intentionally limited to 6..23. Candidate class supports
are fixed discoveries; all weights and dual coefficients are reconstructed
by rational Gaussian elimination without scipy, floating point or any
numerical optimizer. Run from the repository root:
    python notes/sharp-robust-permanent/code/generate_three_subset_certificates.py
Then run the separate standalone Fraction verifier on the JSON output.
"""
from fractions import Fraction as F
from itertools import combinations
from json import dumps
from pathlib import Path


def extend(n, part):
    assert sum(part) <= n
    return tuple(sorted(part + (1,) * (n-sum(part)), reverse=True))


def supports(n):
    if 6 <= n <= 11:
        k = 4
    elif 12 <= n <= 14:
        k = 5
    elif 15 <= n <= 18:
        k = 6
    elif 19 <= n <= 21:
        k = 7
    elif 22 <= n <= 23:
        k = 8
    else:
        raise ValueError(n)
    pos = [extend(n, ()), extend(n, (k,))]
    if n >= 8:
        pos.append(extend(n, (2,) * (n//2) if n%2 == 0
                          else (3,) + (2,)*((n-3)//2)))
    special = {
        6: (3,3), 7: (3,3), 8: (5,3),
        9: (3,3,3), 10: (3,3,3), 11: (3,3,3),
        12: (3,3,3,3), 13: (3,3,3,3), 14: (3,3,3,3),
        15: (4,3,3,3),
        16: (3,3,3,3,3), 17: (3,3,3,3,3),
        18: (4,3,3,3,3), 19: (4,3,3,3,3),
        20: (3,3,3,3,3,3), 21: (3,3,3,3,3,3),
        22: (4,3,3,3,3,3), 23: (4,3,3,3,3,3)
    }[n]
    neg = [extend(n,(2,)),extend(n,special)]
    assert len(set(pos+neg)) == len(pos+neg)
    return pos, neg


def make_perm(part):
    g = []
    first = 0
    for length in part:
        g.extend(first + (i+1)%length for i in range(length))
        first += length
    return g


def stats(n,part):
    g=make_perm(part)
    out=[0,0,0,0]
    for tri in combinations(range(n),3):
        image={g[i] for i in tri}
        overlap=sum(i in image for i in tri)
        out[overlap] += 1
    return out


def exact_linear_system(A,b,nvars):
    assert len(A) == len(b)
    m=[[F(v) for v in row]+[F(rhs)] for row,rhs in zip(A,b)]
    pivots=[]
    cur=0
    for col in range(nvars):
        piv=next((r for r in range(cur,len(m)) if m[r][col]),None)
        if piv is None: continue
        m[cur],m[piv] = m[piv],m[cur]
        pv=m[cur][col]
        m[cur]=[v/pv for v in m[cur]]
        for r in range(len(m)):
            if r==cur:continue
            q=m[r][col]
            if q: m[r]=[u-q*v for u,v in zip(m[r],m[cur])]
        pivots.append(col);cur+=1
    if any(all(v==0 for v in row[:nvars]) and row[-1]!=0 for row in m):
        raise AssertionError('inconsistent exact system')
    if len(pivots)!=nvars:
        raise AssertionError(('underdetermined',pivots,nvars))
    solution=[F(0)]*nvars
    for r,c in enumerate(pivots): solution[c]=m[r][-1]
    assert all(sum(F(a)*v for a,v in zip(row,solution))==rhs
               for row,rhs in zip(A,b))
    return solution


def cert(n):
    pos,neg=supports(n)
    data={p:stats(n,p) for p in pos+neg}
    np=len(pos)
    A=[[1]*np+[0]*len(neg),[0]*np+[1]*len(neg)]
    for j in range(3):
        A.append([data[p][j] for p in pos]+[-data[p][j] for p in neg])
    ans=exact_linear_system(A,[1,1,0,0,0],len(pos+neg))
    pvals=ans[:np];qvals=ans[np:]
    assert all(v>0 for v in ans)

    if n==6:
        lam=[F(0),-F(1,28),-F(3,56)]
        hi,lo=F(1),F(9,14)
    elif n==7:
        lam=[-F(1,35),-F(1,60),-F(9,280)]
        hi,lo=F(1),F(9,14)
    else:
        dualA=[]
        dualB=[]
        for i,p in enumerate(pos+neg):
            dualA.append(data[p][:3]+([1,0] if i<np else [0,1]))
            dualB.append(int(i==0))
        lambdahi=exact_linear_system(dualA,dualB,5)
        lam=lambdahi[:3]
        hi,lo=lambdahi[3:]
    assert hi-lo==pvals[0]
    return dict(n=n,
                P=[dict(cycles=list(p),weight=str(weight))
                   for p,weight in zip(pos,pvals)],
                Q=[dict(cycles=list(p),weight=str(weight))
                   for p,weight in zip(neg,qvals)],
                dual=[str(v) for v in lam],
                lower=str(lo),upper=str(hi),
                optimal_coefficient=str(pvals[0]))


def main():
    results=[cert(n) for n in range(6,24)]
    out=dict(
        metadata='Fixed rational primal-dual certificates for Sn on 3-subsets, 6<=n<=23; generator uses no optimizer. Checker independently enumerates all conjugacy types.',
        degrees=results)
    folder=Path(__file__).resolve().parents[1] / 'certificates'
    folder.mkdir(parents=True,exist_ok=True)
    target=folder/'three_subset_n6_23.json'
    target.write_text(dumps(out,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('WROTE',target,'18 exact rational degree records')
    print('VALUES:',', '.join(str(r['n'])+'='+r['optimal_coefficient'] for r in results))


if __name__=='__main__':
    main()
