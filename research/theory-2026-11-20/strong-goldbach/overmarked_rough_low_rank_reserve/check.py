"""Exact numeric and sign checks for the .223 rough receiver.

No floating-point assertions. Run with python3 -O -B check.py.
"""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement

def check(x, why):
    if not x:
        raise ArithmeticError(why)

D=F(555,1000)
r0=F(223,1000)
rho=F(2501,10000)
theta=F(7,32)
alpha=F(1001,1000)
cap=F(2231,10000)
T=F(55525,10**5)
t=F(1107,10**4)

def arctan_bounds(inv,m):
    a=sum((F((-1)**j,(2*j+1)*inv**(2*j+1)) for j in range(m)),F(0))
    b=a+F((-1)**m,(2*m+1)*inv**(2*m+1))
    return min(a,b),max(a,b)

def exact_numbers():
    check(2*r0<D< T,'physical level')
    check(5*r0>1 and 2<D/r0<4,'rough ranks and initial sieve interval')
    def log_bounds(u,n=8):
        q=(u-1)/(u+1)
        check(0<q<1, "positive log series")
        lb=2*sum((q**(2*j+1)/(2*j+1) for j in range(n)),F(0))
        return lb,lb+2*q**(2*n+1)/((2*n+1)*(1-q*q))
    c0=2/D*log_bounds(D/r0-1)[0]
    check(c0>F(1434,1000),'explicit lower density')
    a2=log_bounds(rho*(1-r0)/(r0*(1-rho)))[1]
    a3=(F(1,2)-2*r0)**2/(2*r0**2)
    a4=(1-4*r0)**3/(144*r0**4)
    neutral=F(400,111)*(a2+a3+a4)
    check(neutral<F(661,1000),'disjoint neutral angular sectors')
    check(2*rho*(c0-F(661,1000))>F(386,1000),'explicit net reserve')
    check(4*r0>2*rho,'rank-three reserve')
    major=[(1+t)/2,(1-(F(3,2)-2*theta)*cap)/(1+theta),1-(alpha*theta+3*cap)/2]
    check(min(major)>T,'major branch')
    minor=[((5-4*theta)-(3-4*theta)*t)/(8-6*theta),(5-alpha*theta-3*t)/8,1-2*t]
    check(all(a>b for a,b in zip(minor,[F(581,1000),F(5561,10**4),F(778,1000)])), 'minor rail endpoints')
    check(min(minor)>(1+t)/2>T,'minor branch')
    check(t<min((1-theta)/(4-3*theta),(1-alpha*theta)/4),'minor branch scope')
    a0,a1=arctan_bounds(5,16)
    b0,b1=arctan_bounds(239,8)
    p0,p1=F(3141592653589793,10**15),F(3141592653589794,10**15)
    check(p0<16*a0-4*b1<=16*a1-4*b0<p1,'Machin pi')
    r=F(347,500)
    # log(2) <= partial geometric arctanh series with explicit positive tail.
    ln2=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(12)),F(0))
    ln2+=F(2,25*3**25)*F(9,8)
    check(ln2+F(4,10**4)/(1-F(4,10**4))<r,'start of overmark')
    bill=(p1**2*(r*r/4-r**3/12+r**5/240)-(r**4/8-r**5/20+r**7/336))/3
    check(bill<F(29964,10**5) and p0**4/120-bill>F(5121,10**4),'angular marginal')
    print('exact lower-density, residue rails, and angular marginal')

def high_mark(t):
    # Actual proof only needs a nondecreasing amplitude 2t v(t).
    return 2*t*max(F(0), min(F(1), F(100)*t-25))

def shape():
    n=0
    for v in combinations_with_replacement(range(1,22),4):
        T=sum(v)
        if not T%2: continue
        u=[F(a,T) for a in v]
        z=-sum(((-1)**len(A)*sum(high_mark(u[i]) for i in A)
                  for j in range(1,5) for A in combinations(range(4),j)
                  if 2*sum(v[i] for i in A)<T),F(0))
        check(z>=0,'no adverse rank-four price')
        n+=1
    print(n,'exact rank-four high-mark sign checks')

if __name__=='__main__':
    exact_numbers()
    shape()
