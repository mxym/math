"""Fixed mixed correspondence checks, not a search."""
from math import isqrt

p,q,b = 1000003,1000006000093,84
def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
assert prime(p) and prime(q)
assert prime(5) and prime(107)
assert 107**2-20*5*107-5**4-124==0
assert 20**2==20**(4*2-2-4) and 124**2<=20**8
assert isqrt(4*124)**2 != 4*124
assert q == p*p+b

A = {(0,1):1,(2,0):-1,(0,0):-b}
B = {(0,1):1,(2,0):1,(1,0):1,(0,0):b}
poly = {}
for (i,j),v in A.items():
    for (k,l),w in B.items():
        poly[i+k,j+l]=poly.get((i+k,j+l),0)+v*w
poly[1,0]+=1
poly[0,0]-=p
poly = {ij:c for ij,c in poly.items() if c}
assert poly == {(0,2):1,(4,0):-1,(1,1):1,(3,0):-1,
                (2,0):-168,(1,0):-83,(0,0):-1007059}
def val(x,y):
    return sum(c*x**i*y**j for (i,j),c in poly.items())
assert val(p,q)==0 and val(q,p)!=0
u,v,C=4,2,32
residual = {ij:c for ij,c in poly.items() if ij not in ((0,2),(4,0))}
for (i,j),c in residual.items():
    gap=u*v-v*i-u*j
    assert gap>=v and abs(c)**v<=C**gap
assert u*v-v-u==v
assert 1003**2 < b*b+p < 1004**2
arithmetic_B=len(residual)*C
N=p*p*q
assert N==1000012000138000612000837 and N.bit_length()==80
assert p>16*N.bit_length()*arithmetic_B==204800
assert p**4 <= N < (p+1)**4
print("PASS: small irreducible mixed relation and separate large-branch exact center")
