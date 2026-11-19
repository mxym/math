"""Exact finite arithmetic checks for the accompanying proofs, Python standard library."""
from fractions import Fraction as Q
from collections import Counter
from itertools import accumulate


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def atoms(n):
    return [1 << d for d in range(n.bit_length()-1,-1,-1) if n & (1 << d)]

# Exhaustive finite dyadic packing, with optional removal of any marked parent
# bit whose halves actually appear in both children.
packed = 0
for left in range(65):
    for right in range(65):
        parent = atoms(left+right)
        inherited = [w for w in parent if w % 2 == 0 and w//2 in atoms(left) and w//2 in atoms(right)]
        for mask in range(1 << len(inherited)):
            removed = {v for j,v in enumerate(inherited) if mask >> j & 1}
            capacities = [w for w in parent if w not in removed]
            a = [w for w in atoms(left) if 2*w not in removed]
            b = [w for w in atoms(right) if 2*w not in removed]
            sizes = sorted(a+b,reverse=True)
            boundaries = set(accumulate(capacities))
            seen = {0}
            lo = 0
            for w in sizes:
                require(lo%w == 0, "alignment")
                lo += w
                seen.add(lo)
            require(lo == sum(capacities) and boundaries <= seen, "packing")
            packed += 1

# Uniform exact mean tile counts: strict random-shift breakpoints form a dyadic
# mesh for dyadic z, so midpoint quadrature here equals the continuum average.
tilechecks = 0
samples = 128
for numerator in range(1,33):
    z = Q(numerator,8)
    for w in [Q(1,8),Q(1,4),Q(1,2),Q(1),Q(2),Q(4)]:
        count = 0
        for k in range(samples):
            a = Q(2*k+1,2*samples)*8
            def contained(w):
                return max(0,int((a+z)//w)-int(a//w)-1)
            maxcount = contained(w) - 2*contained(2*w)
            require(maxcount in (0,1,2), "maximal tiles")
            count += maxcount
        prediction = max(0,z/w-1)-2*max(0,z/(2*w)-1)
        require(Q(count,samples) == prediction, "averaged count")
        tilechecks += 1

# Direct dyadic Kraft costs near every interior dyadic carry tested. Replacing
# its least bit w by the first j smaller bits removes the known tail; D(z-w/2^j)
# is evaluated without using the jump identity.
carry = 0
def cost(a):
    q=a.denominator
    require(q&(q-1)==0,"dyadic")
    d=q.bit_length()-1
    return sum(Q(v,q)*(d-(v.bit_length()-1)) for v in atoms(a.numerator))
for k in range(1,80):
    z=Q(k,32); w=Q(k&-k,32)
    i=cost(w)/w
    for j in range(1,8):
        gap=cost(z-w/(2**j))-cost(z)
        require(gap == 2*w - w*(i+j+2)/(2**j), "carry")
        carry += 1

# An exactly enumerable three-stage mirror of the smooth construction.
# Model only per-cell integrals. Uniform mass on an untreated hole is refined
# into one positive and one negative half giving precisely zero mean.
n=12
total=2**n
vals=[Q(1)]*total
alive=[(0,total)]
holes=[]
for r in (2,3,3):
    nxt=[]
    for l,u in alive:
        d=(u-l)//2**r
        for j in range(2**r):
            lo=l+j*d; hi=lo+d
            if j!=1: nxt.append((lo,hi)); continue
            holes.append((lo,hi))
            for k in range(lo,hi):
                vals[k]+=Q(1 if 2*(k-lo)<d else -1,16)
    alive=nxt
live={k for l,u in alive for k in range(l,u)}
checked=0
for dep in range(9):
    d=total//(2**dep)
    for l in range(0,total,d):
        if any(k in live for k in range(l,l+d)):
            require(sum(vals[l:l+d])==d,"hole cancellation")
            checked+=1
print(f"PASS: {packed} marked dyadic packings; {tilechecks} exact random-shift average counts; {carry} Kraft carry identities; {checked} live-cell integral identities.")
