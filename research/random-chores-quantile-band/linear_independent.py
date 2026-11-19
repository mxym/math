#!/usr/bin/env python3
"""Exact independent finite checks of rectangular colour demands and deletion bounds."""
from itertools import permutations,combinations,product
from fractions import Fraction as F
from math import comb,prod
from collections import Counter
def ck(x):
    if not x:raise ValueError('failed')
def sets(x):
    return [frozenset(u) for i in range(len(x)+1) for u in combinations(x,i)]
def falling(s,t):
    return prod(range(s-t+1,s+1)) if t<=s else 0
def check():
    n=4;k=1;R=set(range(n));B=set(range(n-k));N=len(B);d=3
    occ=[];one=0;trial=0
    for h in range(d):
        H=R-{h};layer=[dict(zip(sorted(H),v)) for v in permutations(B)];occ.append(layer)
        for reverse in range(2):
            SRC=B if reverse else R;TGT=R if reverse else B
            Dst=H if reverse else B;Src=B if reverse else H
            mp=[{j:i for i,j in t.items()} for t in layer] if reverse else layer
            for selected in sets(SRC):
                for target in sets(TGT):
                    t=len(selected)
                    # An omitted prescribed source must make the event impossible.
                    ans=F(falling(len(target&Dst),t),falling(N,t)) if selected<=Src else F(0)
                    emp=F(sum(all(i in p and p[i] in target for i in selected) for p in mp),len(mp))
                    ck(emp==ans);one+=1
    combos=list(product(*occ));tests=0
    for subset in combinations(range(n),2):
      for target in combinations(range(N),2):
       W=set(target)
       for hues in product([(0,1),(0,2),(1,2)],repeat=2):
        expected=F(1)
        for h in range(d):
            demanded={s for s,col in zip(subset,hues) if h in col}
            expected*=F(falling(len(W),len(demanded)),falling(N,len(demanded))) if h not in demanded else 0
        count=sum(all(v in L[h] and L[h][v] in W for v,col in zip(subset,hues) for h in col) for L in combos)
        ck(F(count,len(combos))==expected)
        ck(expected<=F(2,3)**4);tests+=1
    print('rectangular injection exact probabilities (both orientations):',one,'multilayer demand profiles:',tests)
    # At a fixed endpoint, collision excess >=2 has a triple or two disjoint pairs:
    for vals in product(range(4),repeat=6):
        c=Counter(vals);ex=sum(v-1 for v in c.values())
        ck((ex>=2)==(max(c.values())>=3 or sum(v>=2 for v in c.values())>=2));trial+=1
    print('endpoint collision equivalences:',trial)
    # Check pathwise deletion bounds across possible patterns of 24/23 incidences.
    tests=0
    for deg in (23,24):
        for p in ([1]*deg,[2]+[1]*(deg-2)):
            for j in range(1,(1 if deg==23 else 2)+1):
                for S in combinations(range(len(p)),j):
                    ck(sum(p[i] for i in S)<=j+1); tests+=1
    print('admissible local multiplicity-loss cases:',tests)
    val=F(8)*F(12,11)**2*comb(24,3)*F(6,11)**19
    ck(val==F(129164765370544816128,672749994932560009201) and val<F(1,2))
    print('rigorous upper bound on worst union-bound base:',val)
    ck(F(8,3)+F(1,24)/(1-F(1,5))<F(11,4) and F(11,4)**2<8)
    c=0
    for n in range(2,60):
        for k in range(1,n):
            N=n-k
            for s in range(1,N+1):
                if 2*s>n: ck(1<=N-s+1<=n//2); c+=1
    print('large-Hall complementarities, all tested n,k,s:',c)
    print('PASS')
if __name__=='__main__':check()
