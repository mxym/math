#!/usr/bin/env python3
"""Direct signed GHZ action for all raw types and exact converse sanity."""
from itertools import product
from functools import reduce
from operator import xor

def direct_label(t,x):
    # Pauli number p+2z: I,X,Z,XZ. Apply to exact signed
    # computational amplitudes; omit normalization sqrt(2).
    signed=[]
    for ket in [0,7]:
        dest=ket
        amplitude=1
        for i in range(3):
            pauli=t[2*i+((x>>i)&1)]
            if pauli&2 and (ket>>i)&1:
                amplitude=-amplitude
            if pauli&1:
                dest^=1<<i
        signed.append((dest,amplitude))
    signed.sort(key=lambda v: v[0]&1)
    (a,s),(b,z)=signed
    assert a&1==0 and b==a^7
    return (a>>1) | (4*(s!=z))

maps=set()
raw=0
for t in product(range(4),repeat=6):
    labels=tuple(direct_label(t,x) for x in range(8))
    maps.add(labels)
    raw+=1
assert raw==4096 and len(maps)==512
print("direct signed computational GHZ action: 4096 raw types, 512 label maps")

# Given essential f, privacy implies one phase decoder over q.
# Enumerate all extensions of such a decoder to the four q labels
# for every separately obtained deterministic label map.
graphdec=set()
for labels,g in product(sorted(maps),range(16)):
    f=0
    for x,L in enumerate(labels):
        f|=(((L>>2)^((g>>(L&3))&1))<<x)
    graphdec.add(f)

# Independently recover ANF via the Boolean zeta transform.
def anf(f):
    coeff=[(f>>i)&1 for i in range(8)]
    for v in (1,2,4):
        for j in range(8):
            if j&v: coeff[j]^=coeff[j^v]
    return coeff
want=set()
cubics=twos=0
for f in range(256):
    C=anf(f)
    e=sum(C[i] for i in (3,5,6))
    if C[7]:
        cubics+=1
    elif e==2:
        twos+=1
    else:
        want.add(f)
assert graphdec==want and len(want)==80 and cubics==128 and twos==48
print("all graph decoders vs independent ANF: 80 feasible, 128 cubic and 48 two-edge excluded")

def tt(fn): return sum(fn(x&1,(x>>1)&1,(x>>2)&1)<<x for x in range(8))
ps=[tt(lambda x,y,z:int(x+y+z==a)) for a in (1,2)]
ps.extend([tt(lambda x,y,z:x*y^x*z),tt(lambda x,y,z:x*y^x*z^x^z)])
assert all(p not in graphdec for p in ps)
f=ps[-1]
assert all(any((f>>x)&1 != (f>>(x^b))&1 for x in range(8)) for b in (1,2,4))
assert sum((-1)**(((f>>x)&1)^(x.bit_count()&1)) for x in range(8))==0
print("EXACT1, EXACT2, two-edge and all-essential top-Walsh-zero controls PASS")

# Each projected character has a common ignored input, even
# without any assumption on the phase spectrum of the decoded f.
for k in (3,5,7,9,11):
    vectors=[(1<<(k-1))-1]+[1<<j for j in range(k-1)]
    assert reduce(xor,vectors)==0
    for s in range(1<<(k-1)):
        assert any((s&v).bit_count()%2==0 for v in vectors)
    # For even k the all-ones character depends on every party;
    # the odd-party projection proof must not be used there.
    vectors2=[(1<<k)-1]+[1<<j for j in range(k)]
    assert all(v.bit_count()%2 for v in vectors2)
print("character zero-coordinate checks: odd k=3,5,7,9,11 PASS; even negative controls PASS")
