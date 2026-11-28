#!/usr/bin/env python3
"""Exact weights, exact thresholds, and a parity-limit regression."""
from fractions import Fraction as F
from math import comb, e, pi, sqrt

def shells(offsets, r, n):
    step = [offsets.count(k) for k in range(max(offsets)+1)]
    gen = [1]
    for _ in range(n):
        new = [0]*(len(gen)+len(step)-1)
        for j, a in enumerate(gen):
            for k, b in enumerate(step):
                new[j+k] += a*b
        gen = new
    w = [r**(-k) for k in range(len(gen))]
    normalizer = sum(step[k]*w[k] for k in range(len(step)))**n
    return [(j, m, x/normalizer) for j, (m, x) in enumerate(zip(gen, w)) if m]

def optimize(table, f):
    # Optimize via the exact rational active-set intervals, not bisection.
    tail2 = sum(m*w*w for j,m,w in table)
    count, cum = 0, F(0)
    L = Q = None
    prev = None
    for j, m, w in table:
        if L is None and cum + m*w >= f:
            theta = (f-cum)/(m*w)
            L = count+(f-cum)/w
            k = j
        if Q is None and f > cum:
            c = (f-cum)/tail2
            if c*w <= 1 and (prev is None or c*prev >= 1):
                Q = count+c*c*tail2
                g = [min(1,c*y) for j0,m0,y in table]
                assert sum(m0*y*b for (j0,m0,y),b in zip(table,g)) == f
                assert sum(m0*b*b for (j0,m0,y),b in zip(table,g)) == Q
                # Dual bound by completing each one-variable square in [0,1].
                assert 2*c*f + sum(m0*(b*b-2*c*y*b)
                                   for (j0,m0,y),b in zip(table,g)) == Q
        count += m
        cum += m*w
        tail2 -= m*w*w
        prev = w
    assert cum == 1 and tail2 == 0
    assert L is not None and Q is not None and 0<Q<=L and 0<theta<=1
    return L,Q,k,theta

def ceil(x):
    return -(-x.numerator//x.denominator)

small = ties = 0
for steps,r in [([0,1,1],F(2)),([0,1],F(2)),([0,2,5],F(3,2)),
                ([0,0,1,3,4],F(7,5))]:
    for n in range(1,8):
        table = shells(steps,r,n)
        assert sum(m for j,m,w in table) == len(steps)**n
        for target in [F(1,12),F(1,3),F(1,2),F(2,3),F(11,12)]:
            l,q,k,t = optimize(table,target)
            # Direct integer LO feasibility check at consecutive integer lengths.
            def mass(nslots):
                have = F(0)
                for _,m,w in table:
                    used = min(nslots,m)
                    have += used*w
                    nslots -= used
                return have
            assert mass(ceil(l)-1)<target<=mass(ceil(l))
            small += 1
            ties += t==1
assert ties>0

# Independent binomial expressions for the p=(1/2,1/4,1/4) parity example.
# Each k-shell has C(n,k) 2^k strings, each of mass 2^(-n-k).
for n in [40,41,100,101,400,401]:
    k = n//2
    cap = F(1,2) if n%2==0 else F(1)
    table = [(j,comb(n,j)*(1<<j),F(1, 1<<(n+j))) for j in range(n+1)]
    l,q,k0,t = optimize(table,F(1,2))
    l0 = sum(comb(n,j)*(1<<j) for j in range(k))+cap*comb(n,k)*(1<<k)
    assert k0==k and t==cap and l==l0
    parity_ratio = F(17,24) if n%2==0 else F(3,4)
    tol = F(1,20) if n<200 else F(1,220)
    assert abs(F(ceil(q),ceil(l))-parity_ratio)<tol
    if n >=400:
        # The normalized exact continuous LO count differs by parity.
        # Scale its denominator with the largest central power of 2, keeping
        # the intermediate number rational. The only float step is Stirling.
        prefactor = float(l/F(1<<(n+k))) * sqrt(n) / sqrt(2)**(n%2)
        expect = (sqrt(2) if n%2 else 1.5)*sqrt(2/pi)
        assert abs(prefactor-expect)<0.025
        assert abs(float(q/l)-2/e)>0.006

print("EXACT:",small,"rational operational cutoffs,",ties,"exact LO ties")
print("EXACT: six binomial parity cases; classical and LOCC constants differ by parity")
