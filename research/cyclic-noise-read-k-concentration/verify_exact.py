#!/usr/bin/env python3
from fractions import Fraction as Q
from itertools import product
from math import comb

def distribute(n, supports, rates, window):
    block_states = []
    for support, rate in zip(supports, rates):
        states = []
        for mask in range(1 << n):
            weight = mask.bit_count()
            pr = rate**weight * (1-rate)**(n-weight)
            if not pr:
                continue
            shifted_product = 0
            for a in range(n):
                if mask >> a & 1:
                    for b in support:
                        shifted_product ^= 1 << ((a+b) % n)
            states.append((shifted_product, pr))
        block_states.append(states)
    keep = sum(1 << i for i in window)
    ans = [Q(0)] * (len(window)+1)
    for state in product(*block_states):
        result, pr = 0, Q(1)
        for value, weight in state:
            result ^= value
            pr *= weight
        ans[(result & keep).bit_count()] += pr
    return ans

def check(n, supports, rates, window):
    weights = distribute(n, supports, rates, window)
    m = len(window)
    assert sum(weights) == 1 and min(weights) >= 0
    bias = Q(1)
    for support, rate in zip(supports, rates):
        bias *= (1-2*rate)**len(support)
    p = (1-bias)/2
    k = max(sum((a+b) % n in window for b in support)
            for a in range(n) for support in supports)
    assert sum(i*w for i,w in enumerate(weights)) == m*p
    if not m or not k or p in (0,1):
        assert sum(w for i,w in enumerate(weights) if i == m*p) == 1
        return weights, p, k, 0
    count = 0
    for u in (Q(1,3), Q(2,3), Q(2), Q(3)):
        assert sum(w*u**i for i,w in enumerate(weights))**k <= (1-p+p*u**k)**m
        count += 1
    for i in range(m+1):
        q = Q(i,m)
        threshold = (p/q)**i if i else Q(1)
        if i < m:
            threshold *= ((1-p)/(1-q))**(m-i)
        if q <= p:
            assert sum(weights[:i+1])**k <= threshold
            count += 1
        if q >= p:
            assert sum(weights[i:])**k <= threshold
            count += 1
    return weights, p, k, count

def sets(n):
    return [tuple(i for i in range(n) if m >> i & 1)
            for m in range(1 << n)]

cases = comparisons = 0
for n in (1,2,3,4):
    subsets = sets(n)
    for first, second in product(subsets, repeat=2):
        windows = {tuple(range(n)), tuple(range(0,n,2)), ()}
        for window in sorted(windows):
            _,_,_,count = check(n, (first, second), (Q(1,3),Q(1,5)), window)
            comparisons += count
            cases += 1
for rates in product((Q(0),Q(1,2),Q(2,3),Q(1)), repeat=2):
    _,_,_,count = check(4, ((0,2),(0,1)), rates, (0,1,2))
    comparisons += count
    cases += 1
print(f"coefficient enumeration: {cases} cases, {comparisons} exact comparisons")

for n,k in ((4,2),(6,2),(6,3),(8,4)):
    r=n//k
    subgroup=tuple(a*r for a in range(k))
    for ell in range(1,k+1):
        window=tuple(i for i in range(n) if i//r<ell)
        w,p,k_read,_=check(n,(subgroup,),(Q(1,4),),window)
        assert k_read==ell and len(window)==ell*r
        assert w==[comb(r,i//ell)*p**(i//ell)*(1-p)**(r-i//ell)
                   if i % ell==0 else 0 for i in range(ell*r+1)]
        if ell>1:
            assert w[-1]>p**len(window)
print("subgroup: 11 exact full/truncated laws; iid endpoint negative control PASS")

# Prime length, no nontrivial subgroup of size 3: an exact small-bias
# witness that replacing k=3 by k'=2 fails at the lower endpoint.
eta=Q(1,100)
w,p,k,_=check(5,((0,1,3),),(eta,),tuple(range(5)))
assert k==3 and w[0] >= (1-eta)**5
assert w[0]**2 > (1-p)**5
print("prime-length small-bias lower endpoint: reduced-read negative control PASS")
