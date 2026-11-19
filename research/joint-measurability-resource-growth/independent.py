#!/usr/bin/env python3
"""Small exact checks of the algebra and encoding, not of an asymptotic theorem."""
from itertools import product, combinations
from math import comb

def check(v):
    if not v: raise AssertionError("exact check failed")

# For A=[a,x,y; x*,b,z; y*,z*,c], complex Gaussian-integer off diagonal.
# Compare the characteristic-coefficient test to ALL principal minors.
total=singular=positive=0
for a,b,c in product(range(-2,3),repeat=3):
    for r,s,t,u,v,w in product(range(-1,2),repeat=6):
        x2=r*r+s*s; y2=t*t+u*u; z2=v*v+w*w
        minor2=(a*b-x2,a*c-y2,b*c-z2)
        det=a*b*c-a*z2-b*y2-c*x2+2*((r*v-s*w)*t+(r*w+s*v)*u)
        psd = min(a,b,c,*minor2,det)>=0
        coeff = (a+b+c,sum(minor2),det)
        check(psd==(min(coeff)>=0))
        total+=1; positive+=psd; singular+=(psd and det==0)
print("3x3 Hermitians:",total,"; PSD:",positive,"; singular PSD:",singular)

# Four ternary settings: hidden Pauli X/Y pair, a zero padding outcome and
# two spectator settings. F for all words has scalar 5 and Pauli vector
# (3*x,4*y,0). Both three-valued signs x,y include the zero padding label.
# Validation uses qubit det(tI+A)=t^2+2at+(a^2-|v|^2).
words=bd=0
for z in product((-1,0,1),repeat=4):
    x,y=z[1],z[3]
    coeff=(10,25-9*x*x-16*y*y)
    check(min(coeff)>=0)
    words+=1; bd+=coeff[1]==0
check(words==81 and bd==36)
# M_{±} = (I ± P)/2; F_{±}=aI-b(±P); F_0=aI but M_0=0.
witness_pairing=sum(2*(a-b) for a,b in [(2,3),(3,4)])
check(witness_pairing==-4)
print("Padded 4-setting dual certificate:",words,"full words;",bd,"singular; pairing",witness_pairing)

# Form all coordinate masks for the middle-layer models n=4 and 5.
families=0
for n in (4,5):
    k=n//2; middle=[s for s in range(1<<n) if s.bit_count()==k]
    base=sum(1<<s for s in range(1<<n) if s.bit_count()<k)
    seen=set()
    for flags in range(1<<len(middle)):
        v=base+sum(1<<s for i,s in enumerate(middle) if flags&(1<<i))
        for j in range(n): check(v&(1<<(1<<j)))
        # Check downward closure by deleting one vertex.
        for s in range(1<<n):
            if v&(1<<s):
                for j in range(n):
                    if s&(1<<j): check(v&(1<<(s^(1<<j))))
        seen.add(v)
    check(len(seen)==1<<comb(n,k))
    families+=len(seen)
print("independent middle-layer masks tested:",families)
