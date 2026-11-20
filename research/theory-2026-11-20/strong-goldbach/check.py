"""Small exact illustrations only; the asymptotic proofs are in the notes."""
from fractions import Fraction as F
from math import isqrt

def prime(n):
    return n >= 2 and all(n % d for d in range(2,isqrt(n)+1))
def categories(N):
    r1,r2=[],[]
    for x in range(3,N-4,2):
        y=N-x
        a,b,c,d=map(prime,(x,x+2,y,y-2))
        if a and b and not c and d: r1.append(x)
        if not a and b and not c and not d: r2.append(x)
    return r1,r2

assert all(prime(p) and p%105==2 for p in [107,317,947])
for N in [1150,1360,1570,1780,1990]:
    assert N%210==100
    u,v=categories(N)
    assert not u and {105,315,945}<=set(v)
    print(N, 'R1',len(u),'R2',len(v), 'explicit R2 witnesses 105,315,945')
for p in [2,3,5,7,11,13,17]:
    def b(r):
        return F(p*sum(x%p!=0 and (r-x)%p!=0 for x in range(p)),(p-1)**2)
    assert sum(b(r) for r in range(p))/p==1
    assert sum(b(r)**2 for r in range(p))/p==1+F(1,(p-1)**3)
print('all local first and second factor identities passed')
