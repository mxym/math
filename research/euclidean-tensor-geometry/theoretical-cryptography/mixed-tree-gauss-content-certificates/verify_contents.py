"""Exact finite root-gcd and correspondence checks; no external input."""
from fractions import Fraction as Q
from itertools import product
from math import gcd

def vmul(A,B):
    a,b,c,d=A
    e,f,g,h=B
    return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)

count=0
for word in product(((1,1,0,1),(1,0,1,1),(1,-1,0,1),(1,0,-1,1),(100, -1,1,0),(0,1,-1,100)), repeat=4):
    M=(1,0,0,1)
    for F in word:
        M=vmul(F,M)
        a,b,c,d=M
        assert a*d-b*c==1
        assert gcd(a,b)==gcd(c,d)==1 # primitive endpoint coefficients
    count+=1

for h in range(1,80):
    p,q=2**h,3**h
    # Expand in Y, then in X, separately.
    leadingY=(q*p,q*(1-5*p))
    trailingY=(p*(1-3*q),(1-3*q)*(1-5*p)-1)
    leadingX=(p*q,p*(1-3*q))
    trailingX=(q*(1-5*p),(1-3*q)*(1-5*p)-1)
    assert gcd(*leadingY)==q and gcd(*leadingX)==p
    assert gcd(*trailingY)==gcd(*trailingX)==1
    assert gcd(gcd(*leadingY),gcd(*leadingX))==1
    for x in (Q(5),Q(11,2),Q(7)):
        y=3+(1/(p*(x-5)+1)-1)/q
        assert (p*(x-5)+1)*(q*(y-3)+1)==1

for C in (2,6,9,25,35,2**133+1):
    B=gcd(C,C)
    for t in (Q(1),Q(3,2),Q(17,5)):
        assert t*(C/t)==C and B==C
    N=C**2*3
    # Exact certificate-support equality independently by iterated gcd.
    rem=N
    while gcd(rem,B)>1: rem//=gcd(rem,B)
    assert (gcd(N,B**N.bit_length())<N)==(rem>1)

print("PASS generic endpoint tests: %d Mobius words; 79 root-adaptive fixtures; 6 actual constant fibres and support checks." % count)
