#!/usr/bin/env python3
"""Exact max-violation slicing and direct retained-transcript experiments."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from random import Random


def indexsets(n):
    return [idx for k in range(n+1) for idx in combinations(range(n), k)]


def marginal(weights, ids):
    sums = defaultdict(int)
    for x,w in weights.items():
        sums[tuple(x[i] for i in ids)] += w
    return sums


def partition(weights, Ns, r, gamma):
    total = sum(weights.values())
    residual = dict(weights)
    out = []
    denom = {J: 2 ** sum(r[i] for i in J) for J in indexsets(len(Ns))}
    cap = F(max(weights.values()), total)
    while sum(residual.values()) >= gamma*total:
        mass = sum(residual.values())
        pick = next(((J,a) for J in reversed(list(denom)) if J
                     for a,w in sorted(marginal(residual,J).items())
                     if w*denom[J] > mass), ((),()))
        J,a = pick
        comp = {x:w for x,w in residual.items() if tuple(x[i] for i in J)==a}
        assert comp
        for x in comp: del residual[x]
        compmass = sum(comp.values())
        for A in denom:
            if not set(A).intersection(J):
                assert max(marginal(comp,A).values())*denom[A] <= compmass
        assert F(prod(Ns[i] for i in J),denom[J]) <= cap*prod(Ns)/gamma
        out.append((J,a,comp,False))
    assert sum(residual.values()) < gamma*total
    if residual:
        out.append(((),(),residual,True))
    assert sum(len(c) for J,a,c,e in out)==len(weights)
    assert {x:w for J,a,c,e in out for x,w in c.items()}==weights
    return out


def transcript(weights, Ns, r, gamma, shared=False):
    if all(x & (x-1)==0 for x in Ns):
        # Independent uniform binary inner-product seeds are two-universal.
        # The exact kernel is 2 on the diagonal and 1 everywhere else.
        for N in Ns:
            assert all(sum(((s&x).bit_count()-(s&y).bit_count())%2==0
                           for s in range(N))*2 == (2 if x==y else 1)*N
                       for x in range(N) for y in range(N))
    else:
        raise AssertionError("fixture alphabets must be powers of two")
    parts = partition(weights,Ns,r,gamma)
    total = sum(weights.values())
    n = len(Ns)
    if shared:
        assert all(N==Ns[0] for N in Ns)
        seeds = [(s,)*n for s in range(Ns[0])]
    else:
        seeds = list(product(*(range(N) for N in Ns)))
    real, ideal = defaultdict(int), defaultdict(int)
    for J,a,comp,exc in parts:
        I = [i for i in range(n) if i not in J]
        fresh = list(product(range(2),repeat=len(I)))
        for x,w in comp.items():
            for s in seeds:
                y = tuple((a0&b0).bit_count()%2 for a0,b0 in zip(x,s))
                real[J,a,s,y] += F(w,total*len(seeds))
                for u in fresh:
                    y0 = list(y)
                    for i,z in zip(I,u): y0[i]=z
                    ideal[J,a,s,tuple(y0)] += F(w,total*len(seeds)*len(fresh))
    assert sum(real.values())==sum(ideal.values())==1
    # Check public chosen positions, their raw values, their unmodified
    # outputs, and the entire seed law jointly before checking full TV.
    partial = []
    for d in (real,ideal):
        m = defaultdict(int)
        lab = defaultdict(int)
        for (J,a,s,y),p in d.items():
            m[J,a,s,tuple(y[i] for i in J)] += p
            lab[J,a] += p
        for (J,a,s,yJ),p in m.items():
            assert p==lab[J,a]/len(seeds)
        partial.append(m)
    assert partial[0]==partial[1]
    tv = sum(abs(real.get(k,0)-ideal.get(k,0))
             for k in real.keys()|ideal.keys())/2
    if not shared:
        bound = prod(1+F(1,2**ri) for ri in r)-1
        assert tv <= gamma or 4*((tv-gamma)/(1-gamma))**2 <= bound
    return parts,tv


def main():
    rng = Random(670103)
    main_support = {(0,y,z):4 for y in range(4) for z in range(4) if (y^z)%2==0}
    main_support[(3,0,1)] = 1
    parts,tv = transcript(main_support,(4,4,4),(1,1,1),F(1,8))
    assert len(parts)==2 and parts[0][0]==(0,) and parts[1][3]
    assert tv < F(1,2)
    count = 1
    for Ns,r in (((4,4),(1,1)), ((4,4,4),(1,1,0)), ((2,4,8),(0,1,2))):
        pts = list(product(*(range(N) for N in Ns)))
        for _ in range(8):
            src = {x:rng.randint(1,6) for x in rng.sample(pts,rng.randint(1,len(pts)))}
            transcript(src,Ns,r,F(rng.randint(1,4),8))
            count += 1
    print(f"independent PASS: {count} direct weighted partition/transcript tests, including dependent free blocks and exceptional tail")

    cases = 0
    for t,z,k,m,n,alpha7 in product((1,2,4,8),(0,1,3),(0,2,4),(0,1,2),
                                     (13,20),range(8)):
        eps = F(1,2**z)
        r = k+m+t.bit_length()+1+2*z
        if r>=n: continue
        eta = eps**2/F(4*t*2**m)
        cap = (1+2**m*eta+F(2**(m+k),2**r))**t-1
        assert cap<=eps**2
        Dbudget = (1-F(alpha7,7))*t*n+z+1
        countI = max(0,t-Dbudget//(n-r))
        assert countI==t-max(i for i in range(t+1) if i*(n-r)<=Dbudget)
        cases += 1
    print(f"independent PASS: {cases} exact binary parameter and integer-budget checks")

    # Shared seed is a different model. With X=(Z,Z), the output is always
    # diagonal, whereas two independent ideal binary outcomes are not.
    dupl = {(z,z):1 for z in range(16)}
    _,tv_s = transcript(dupl,(16,16),(2,2),F(1,64),True)
    _,tv_i = transcript(dupl,(16,16),(2,2),F(1,64))
    assert tv_s==F(33,64) and tv_i < F(1,2)
    for t in range(1,7):
        for B in range(1,t+1):
            selected = range(B)
            actual = F(0)
            for tags in product(range(2),repeat=t):
                prob = prod(F(1,4) if tag else F(3,4) for tag in tags)
                actual += prob*F(1,2**sum(tags[i] for i in selected))
            assert 1-actual==1-(1-F(1,8))**B
    print("independent PASS: shared-seed exclusion and rare public-tag accumulation controls")


if __name__=="__main__":
    main()
