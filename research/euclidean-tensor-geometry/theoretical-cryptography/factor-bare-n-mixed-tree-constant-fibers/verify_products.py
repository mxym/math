"""Independent finite checks of Sylvester resultants and endpoint units."""
from fractions import Fraction as Q
from itertools import product
from math import prod

def det(mat):
    a=[list(map(Q,row)) for row in mat]
    n=len(a)
    out=1
    for i in range(n):
        j=next((j for j in range(i,n) if a[j][i]),None)
        if j is None: return 0
        if j!=i:
            a[j],a[i]=a[i],a[j]
            out=-out
        piv=a[i][i]
        out*=piv
        for j in range(i+1,n):
            c=a[j][i]/piv
            for h in range(i,n): a[j][h]-=c*a[i][h]
    return out

def res(A,B):
    # inputs descending, possibly specialized leading zero in B
    n,m=len(A)-1,len(B)-1
    rows=[[0]*i+A+[0]*(m-1-i) for i in range(m)]
    rows += [[0]*i+B+[0]*(n-1-i) for i in range(n)]
    return det(rows)

def poly(a,b): # integer quadratic with prescribed rational roots
    d=a.denominator*b.denominator
    return [d,int(-d*(a+b)),int(d*a*b)]

pairs=[(Q(2,3),Q(-7,5)),(Q(-1),Q(1)),(Q(3,2),Q(3,2))]
powers=joins=units=0
for (a,b),e,z in product(pairs,range(1,6),range(-5,6)):
    A=poly(a,b)
    v=res(A,[-1]+[0]*(e-1)+[z])
    assert v==A[0]**e*(z-a**e)*(z-b**e)
    powers+=1
for (a,b),(c,d),z in product(pairs,pairs,range(-5,6)):
    A,B=poly(a,b),poly(c,d)
    # W^2 B(z/W) = B[2] W^2 + B[1] z W + B[0] z^2.
    v=res(A,[B[2],B[1]*z,B[0]*z*z])
    want=(A[0]*B[0])**2*prod(z-i*j for i in (a,b) for j in (c,d))
    assert v==want
    joins+=1
for roots in pairs:
    A=poly(*roots)
    for p in (2,3,5,7,11,13,17):
        if (A[0]*A[-1])%p==0: continue
        for x in roots:
            assert x.numerator%p and x.denominator%p
            units+=1

# At the two conjugate roots of Y^2-2, the squared values coincide.
for z in range(-8,9):
    assert res([1,0,-2],[-1,0,z])==(z-2)**2
    assert res([1,0,-2],[-2,0,z*z])==(z*z-4)**2

# Both components of (xy-15)(y-x-2)=0 pass through (3,5),
# but their monomial is respectively constant and nonconstant generically.
for x in map(Q,(1,2,3,4,7)):
    for y in (15/x,x+2):
        assert (x*y-15)*(y-x-2)==0
    assert x*(15/x)==15
    assert (x*(x+2)==15)==(x==3)

print("PASS product determinants: %d powers; %d pair products; %d unit tests; 34 conjugate checks; reducible mixed fixture." % (powers,joins,units))
