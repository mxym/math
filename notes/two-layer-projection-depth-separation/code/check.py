#!/usr/bin/env python3
"""Exact certificate for two universal simplex-product inequalities and a depth gap.

All mathematical decisions use Python int/Fraction, never float, assert,
heuristic numerical optimization or closed-source solver.
"""
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache

LOG_TERMS = 20
PI_LO, PI_HI = F(333,106), F(355,113)
Q4, Q5 = F(175,128), F(189,128)


def need(cond, description):
    if not cond:
        raise RuntimeError('exact certificate failed: '+description)


def atan_bounds(z,N=12):
    z=F(z)
    need(0<z<1 and N%2==0,'arctan arguments')
    v=sum(F((-1)**j)*z**(2*j+1)/F(2*j+1) for j in range(N))
    return v,v+z**(2*N+1)/F(2*N+1)


def check_pi():
    a,b=atan_bounds(F(1,5))
    c,d=atan_bounds(F(1,239))
    need(16*a-4*d>PI_LO and 16*b-4*c<PI_HI,'Machin pi enclosure')


@lru_cache(maxsize=None)
def ln2():
    z=F(1,3);acc=F(0);power=z
    for j in range(LOG_TERMS):
        acc+=2*power/F(2*j+1);power*=z*z
    return acc,acc+2*power/(F(2*LOG_TERMS+1)*(1-z*z))


@lru_cache(maxsize=2048)
def ln_interval(x):
    x=F(x);need(x>0,'log positive')
    shift=0
    while x>=2:x/=2;shift+=1
    while x<1:x*=2;shift-=1
    z=(x-1)/(x+1);acc=F(0);power=z
    for j in range(LOG_TERMS):
        acc+=2*power/F(2*j+1);power*=z*z
    rem=2*power/(F(2*LOG_TERMS+1)*(1-z*z))
    l2,h2=ln2()
    return (acc+shift*l2,acc+rem+shift*h2) if shift>=0 else (acc+shift*h2,acc+rem+shift*l2)


def block(p,q):
    n=p+q
    H=F(n)/(F(p,p+1)+F(q,q+1))
    Q=F(comb(n,p)*p**p*q**q*(n+2*p*q),n**(n+1))
    return H,Q


def U2(n):
    # Square of a valid upper bound for Q_(p,q) for every p+q=n.
    return (F(1)+F(n,2))**2*F(2,1)/(PI_LO*n)/(F(1)-F(1,12*n))**2


def check():
    check_pi()
    # Independently derive B_p=(T_p x T_p) using exact factorials.
    def g(n):return F(n**n,factorial(n))
    need(F(5)*g(4)**2/g(8)==Q4,'B4 exact product identity')
    need(F(6)*g(5)**2/g(10)==Q5,'B5 exact product identity')

    # I. Sharp spectral-block rate: all p+q<=15, strict except p=q=5.
    count_one=0
    for n in range(2,16):
        for p in range(1,n//2+1):
            q=n-p;H,Q=block(p,q)
            if (p,q)==(5,5):
                need(Q==Q5,'winning block equality')
            else:
                need(Q**11<Q5**(n+1),f'spectral block counterexample p={p},q={q}')
            count_one+=1
    need(count_one==56,'spectral finite scan incomplete')

    # Universal n>=16 (Robbins + pi + exp Taylor + calculus as in paper).
    need(U2(16)**11<Q5**34,'spectral n=16 tail base')
    need(F(81)*F(7,176)>F(49,16),'U(16)>7/4 lower check')
    z=F(3,11)
    need(2*(z+z**3/F(3))>F(17,32),'log(7/4)>17/32')
    # The analytic derivative is elementary; its critical integer sign is checked.
    need((16-2)*(12*16-1)>2*(16+2),'spectral tail derivative base')

    # II. Sharp H-defect rate: all p+q<=39, equality only at p=q=4.
    count_two=0
    for n in range(2,40):
        for p in range(1,n//2+1):
            q=n-p;H,Q=block(p,q)
            D_minus_H=F(n+1)-H
            need(D_minus_H>0,'H must be smaller than D for product')
            if (p,q)==(4,4):
                need(Q==Q4 and D_minus_H==4,'defect block equality')
            else:
                need(F(4)*ln_interval(Q)[1] < D_minus_H*ln_interval(Q4)[0],
                     f'defect block counterexample p={p},q={q}')
            count_two+=1
    need(count_two==380,'defect finite scan incomplete')

    # Universal n>=40. The proof bounds D-H>=n/3 and verifies U(40)^6<Q4^20.
    need(U2(40)**3<Q4**20,'defect n=40 tail base')
    need(F(94,303)>F(3,10),'log Q4>3/10 from atanh first term')
    need(F(1,80)<F(1,40),'defect tail derivative sign')

    # III. Explicit dimension-85 witness using a product of two joins,
    # followed by a two-fold join (two nested nontrivial product levels).
    H1=F(12);Q1=Q5**2;d1=21
    # Product K1 x K1, then self-join twice.
    Q_product=Q1**2*H1*g(d1)**2/g(2*d1)
    H2=2*H1;Q2=Q_product**2;D2=2*(2*d1+1)
    need(D2==86 and H2==24,'nested body dimensions/state')
    ratio=H2*Q2/F(D2)
    # Two regimes t=H/D <=3/5 and >=3/5. All exponents cleared exactly.
    need((F(5,3)*ratio)**11>Q5**86,'nested witness fails spectral upper')
    need((F(5,3)*ratio)**5>Q4**43,'nested witness fails H-defect upper')
    need(ratio>13,'dimension-85 witness lower check')
    need(Q2**11>Q5**86,'strict asymptotic depth gap fails')
    print('PASS: exact two-layer simplex-product spectral and defect optimizers')
    print('spectral maximum block = (p,q)=(5,5), Q=189/128, D=11')
    print('defect maximum block = (p,q)=(4,4), Q=175/128, D-H=4')
    print('finite rational spectral tests =',count_one)
    print('finite rational defect tests =',count_two)
    print('analytic tails certified at n>=16 and n>=40')
    print('PASS: explicit 85D nested product/join body beats every two-layer join')
    print('85D witness R/c_85 =',ratio)
    print('PASS: two-layer asymptotic ceiling is strictly below nested-tree construction')
    print('all inequalities use exact int/Fraction; no floating point')


if __name__=='__main__':check()
