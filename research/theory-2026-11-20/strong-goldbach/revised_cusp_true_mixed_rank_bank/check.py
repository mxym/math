"""Exact finite checks for the actual revised high-by-high bank."""
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial

def demand(s,name):
    if not s:
        raise ArithmeticError(name)

def subs(k):
    for j in range(k+1):
        yield from combinations(range(k),j)

def Z(t,phi,g):
    return -sum(((-1)**len(a)*g(sum(t[i] for i in a))*sum(phi(t[i]) for i in a)
                 for a in subs(len(t))), Q(0))

def F(t):
    return sum(((-1)**len(a)*abs(sum(t[i] for i in a)-sum(t)/2)
                 for a in subs(len(t))), Q(0))

def A(t):
    return sum(((-1)**len(a)*max(0,sum(t)-2*sum(t[i] for i in a))
                 for a in subs(len(t))), Q(0))

def angular():
    center=[Q(a,1000) for a in [50,177,215,267,291]]
    width=Q(4,10000)
    for sign in product([-1,1],repeat=5):
        t=[a+b*width for a,b in zip(center,sign)]
        h=sum(t)/2
        longs=[u for u in combinations(range(5),2) if sum(t[i] for i in u)>h]
        demand(longs==[(2,4),(3,4)],'rank-five graph')
        g0=lambda v: Q(v<Q(4997,10000))
        g1=lambda v: Q(v<h)
        for a in subs(5):
            u=sum(t[i] for i in a)
            demand(u!=h and g0(u)==g1(u),'literal root collar box')
        z0=Z(t,lambda u:2*u,g0)
        zH=Z(t,lambda u:2*u*Q(u>Q(25008,10**5)),g0)
        demand(F(t)==0 and z0==-2*sum(t) and zH==-2*sum(t[-2:]),'two true source weights')
    # Stored exponent tuples have an exact own-half orientation and
    # a tagged least prime that cannot be a polynomial mark.
    tested=0
    for v in combinations(range(2,16),4):
        t=[Q(1,1200)]+[Q(i,100) for i in v]
        for k in range(2,6):
            vv=t[:k]
            phi=lambda u:2*u*Q(u>Q(1,100))
            g=lambda u: Q(u<Q(1,2))
            base=vv[1:]
            z=Z(vv,phi,g)
            zz=sum((phi(base[j])*sum(((-1)**len(a)*(
                  g(base[j]+sum(base[i] for i in a))-g(base[j]+sum(base[i] for i in a)+vv[0]))
                for a in subs(len(base)) if j not in a), Q(0))
                for j in range(len(base))),Q(0))
            demand(zz==z,'literal least-bit difference')
            if sum(vv)>0 and k>=2:
                demand(A(vv)==F(vv),'own-root even parity identity')
            tested+=1
    print('32 strict source box corners and',tested,'exact marked/own-root replays')

def log_lb(z,n=16):
    a=(z-1)/(z+1)
    demand(0<=a<1,'positive log series')
    return 2*sum((a**(2*j+1)/(2*j+1) for j in range(n)),Q(0))

def rails():
    f=Q(5085,10**4)
    demand(f<Q(1,2)+Q(496,10**4)/2,'Fouvry square-root rail')
    demand(f<Q(4,7)-Q(6,7)*Q(504,10**4),'Fouvry 4/7 rail')
    q=Q(501,1000)
    a=Q(1,2)+Q(7,10)*q+Q(1,4)*q
    b=Q(1,2)+Q(6,10)*q+Q(35,100)*(2*q-1+q)
    a2=Q(51,100)+Q(7,20)+Q(1,4)*q
    b2=Q(51,100)+Q(3,10)+Q(7,20)*q
    demand(max(a,b,a2,b2,Q(99,100))+Q(1,1000)<Q(995,1000),'joint CRT floors and all rough allocations')
    # For every true t0/δ in [1/2,1] the transformed interval
    # includes [1/R, R/2]. At t0/s<1 the Dickman area is exact:
    # ρ=0 below 0 and 1 on [0,1].
    for R in [2,3,10,100,1000]:
        for k in range(51):
            u=Q(50+k,100)
            demand(u/R<=Q(1,R) and u*R>=Q(R,2), 'uniform Dickman band')
    for k in range(100):
        v=Q(k,100)
        area=max(Q(0),min(Q(1),v)-max(Q(0),v-1))
        demand(area==v, 'Dickman area below first unit')
    # Small-R branch numerics from the original strict band retained for comparison.
    demand(log_lb(Q(2))/4>Q(17,100),'original narrow bank')
    print('exact Fouvry/CRT exponents and both Dickman band endpoint checks')

if __name__=='__main__':
    angular()
    rails()
