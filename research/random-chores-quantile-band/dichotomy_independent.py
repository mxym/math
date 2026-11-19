#!/usr/bin/env python3
"""Finite, exact checks of the fixed-law threshold criterion's arithmetic and edge cases."""
from fractions import Fraction as R
from math import isqrt, comb
from itertools import combinations
def ck(x):
    if not x:raise ValueError('failed')

# This continuous CDF has a plateau and no strict inverse there. Its left quantile
# is the one appearing in the mathematical statement.
def cdf(x):
    x=R(x)
    return 0 if x<0 else 2*x if x<=R(1,4) else R(1,2) if x<=R(1,2) else min(1,x)
def quant(u):
    ck(0<u<1)
    return u/2 if u<=R(1,2) else u
def run():
    checked=0
    for den in range(2,101):
        for i in range(1,den):
            u=R(i,den);x=quant(u);ck(cdf(x)==u)
            if u<=R(1,4):ck(cdf(2*x)==2*u)
            checked+=1
    ck(quant(R(1,2))==R(1,4))
    print('flattened continuous CDF: generalized quantile identities:',checked)
    # For F(x)=2^(1-1/x) at x_j=1/(8j), both masses and m_j are exact.
    case=0;floorcount=0
    for j in range(1,49):
        u=R(1,2**(8*j-1));v=R(1,2**(4*j-1));m=2**(6*j-1)
        ck((m*m)*u*v==1 and m*u==R(1,2**(2*j)) and m*v==2**(2*j))
        for K in (2,3,20,100):
            mu=m*(v-u)
            if j>=6:
                ck(mu>K and m*u+mu/(mu-K)**2<R(1,10))
            case+=1
        for c in (R(101,100),R(3,2),R(199,100),R(1999,1000)):
            n=m//c
            if n:
                ck(c*n<=m<c*(n+1))
            if j>=4:
                ck(n<m<2*n and R(m,n)>=c);floorcount+=1
    print('rapid-tail exact certificates:',case,'floor/density strict-range certificates:',floorcount)
    # Constant positive lower endpoint atomless uniform [1/2,1]: F(2Q)=1 for all u.
    for j in range(2,50):
        u=R(1,j**4);m=j*j;Q=(1+u)/2
        ck(2*Q>1 and m*m*u==1 and m*u==R(1,j*j) and m>=j)
    print('positive lower-endpoint quantile examples:',48)
    # No equality threshold is smuggled in: even the least p/c=0.9/2 exceeds 1/e since e>5/2.
    ck(R(9,20)>R(2,5));print('finite-depth no-fixed-point strictness checked')
    print('PASS')
if __name__=='__main__':run()
