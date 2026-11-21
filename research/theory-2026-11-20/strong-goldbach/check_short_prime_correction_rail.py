"""Finite exact checks of the post-lift coefficient; no analytic bounds are tested."""
from fractions import Fraction
from math import gcd,prod
def phi(n):
    return sum(gcd(i,n)==1 for i in range(1,n+1))
def mob(n):
    b=1
    p=2
    while p*p<=n:
        if n%p==0:
            n//=p
            if n%p==0:return 0
            b=-b
        p+=1
    return b if n==1 else -b
def ram(q,n):
    return sum(d*mob(q//d) for d in range(1,q+1) if q%d==0 and n%d==0)
def run():
    ncase=nzero=nnonzero=0
    for q in (2,4,6,8,10,12,16,18,22,24,30,32,36,42):
        for d in range(1,21):
            v=q*d
            unit=[a for a in range(v) if gcd(a,v)==1]
            # Ordered long-prime residue-pair sum histogram, entirely over Z.
            counts=[0]*v
            for a in unit:
                for b in unit:counts[(a+b)%v]+=1
            for N in range(0,2*q+6,2):
                B=sum(gcd(a,q)==1 and gcd(N-a,q)==1 for a in range(q))
                direct=Fraction(mob(d)*sum(counts[j]*ram(d,(j-N)//q) for j in range(N%q,v,q)),phi(d)*len(unit)**2)
                expect=Fraction(0) if gcd(d,q)>1 else Fraction(B*mob(d)**3*ram(d,N),phi(q)**2*phi(d)**3)
                if direct!=expect:raise ArithmeticError((q,d,N,direct,expect))
                ncase+=1
                if direct:nnonzero+=1
                else:nzero+=1
    print(f"PASS {ncase} coefficient checks: {nnonzero} nonzero, {nzero} zero")
if __name__=='__main__':run()
