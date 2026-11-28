"""Exact integer tables for the order-2396 signed-automorphism note."""
from itertools import combinations_with_replacement
from math import gcd, isqrt

if not __debug__:
    raise RuntimeError("Run without -O")

N = 2396
ELL = 599

def isprime(p):
    return p > 1 and all(p % d for d in range(2, isqrt(p) + 1))

def contains_conjugation(a, m):
    if gcd(a, m) != 1:
        return False
    z = a % m
    while z != 1:
        if z == m - 1:
            return True
        z = (z * a) % m
    return False

def square(k):
    return k >= 0 and isqrt(k)**2 == k

def fixed_gram_test(f, q):
    """Only the necessary small-block restrictions in the note."""
    if f <= 1:
        return True
    if f < q or (f % 2 == 0 and f < 2*q):
        return f == 2 or f % 4 == 0
    if f % 2 == 1 and q <= f < 3*q:
        if (f-q) % 4:
            return f-(f-1)*q >= 0
        if f > q:
            return square(f+(f-1)*q)
    return True

def cycle_test(n, q, f, t, ell=None):
    if n != f+q*t or (t and q*f > n) or not fixed_gram_test(f, q):
        return False
    if f >= 2 and (f < q or (f % 2 == 0 and f < 2*q)):
        if t % (2 if f == 2 else 4):
            return False
    if ell is not None and n % (ell*ell) != 0 and t % 2:
        if contains_conjugation(ell, q):
            return False
    return True

primes = [q for q in range(3, N+1, 2) if isprime(q)]
cycles = {}
for q in primes:
    a = []
    for f in range(N//q+1):
        t, rem = divmod(N-f, q)
        if rem or t == 0 or not cycle_test(N,q,f,t,ELL):
            continue
        a.append(f)
    if a:
        cycles[q] = a

# 479 is additionally excluded by Davis's theorem, not by these filters.
expected_large_pre = {29:[76],31:[40],37:[28],59:[36],
                      149:[12],199:[8],479:[1],599:[0]}
assert {q:fs for q,fs in cycles.items() if q >= 29} == expected_large_pre
assert 479 in cycles
del cycles[479]
large = {q:(fs[0],(N-fs[0])//q) for q,fs in cycles.items() if q >= 29}
assert all(t % q != 0 for q,(f,t) in large.items())
print("large primes", large)

def pair_list(p,r):
    f,t=large[p]
    defect=t-f
    out=[]
    for fr in cycles[r]:
        for s in range(f % r, min(f,fr)+1, r):
            if (fr-s) % p:
                continue
            z,rem=divmod(N-f-fr+s,p*r)
            if rem or z < 0:
                continue
            if z % 2 and contains_conjugation(ELL,p*r):
                continue
            a=(f-s)//r
            k=z-a
            if k<0 or (r-1)*k>defect:
                continue
            if defect==4:
                if k > (1 if r==3 else 0):
                    continue
                if z:
                    f_small=t-r*z
                    ell=5 if t in (40,80) else None
                    if not cycle_test(t,r,f_small,z,ell):
                        continue
            out.append((fr,s,z,k))
    return out

pairs={p:{r:pair_list(p,r) for r in cycles if r!=p} for p in large}
cols={p:[r for r,ws in x.items() if ws] for p,x in pairs.items()}
assert cols == {29:[3,5,19],31:[3,5,7,19],37:[3,5,7],59:[3,5],
                149:[3],199:[],599:[]}
assert pairs[149][3]==[(596,0,4,0)]
print("centralizer primes other than self", cols)

def row_sum_possible(q, order):
    f,t=large[q]
    k=N-q*f
    odds=[a for a in range(1,isqrt(k)+1,2) if a % (2*order) in (1,2*order-1)]
    # Subtract the baseline t entries of absolute value 1.
    excess=k-t
    big=[a*a-1 for a in odds if a>1 and a*a-1<=excess]
    return any(sum(v)==excess for d in range(min(t,excess//min(big,default=excess+1))+1)
               for v in combinations_with_replacement(big,d))

for q,r in [(29,7),(59,29),(149,37),(199,11),(199,9),(599,13),(599,23)]:
    assert not row_sum_possible(q,r)

# Induced actions on the completed small row block for q=29, r=7.
assert [a for a in range(1,76//7+1) if cycle_test(80,7,80-7*a,a,5)]==[]
# For q=59, r=29: overlap constraint f_r=(f+t)-2ra.
assert [a for a in range(36//29+1) if 76-58*a in cycles[29]]==[0]
# At q=199, an induced nontrivial order-three action on 8/12 labels
# leaves exactly 5 actual fixed positions, impossible by the fixed Gram.
induced=[(a,z,20-3*(a+z)) for a in range(3) for z in range(1,a+2)
         if cycle_test(12,3,12-3*z,z)]
assert induced==[(2,3,5)]
assert not fixed_gram_test(5,3)
print("normalizer orbit-norm exclusions and induced block actions OK")
