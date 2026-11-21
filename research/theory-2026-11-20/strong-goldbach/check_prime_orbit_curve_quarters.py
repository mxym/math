"""Exact polynomial identity tests for the last section; plain Python 3, -O safe."""
from fractions import Fraction as Q
from itertools import product


def need(cond):
    if not cond:
        raise ArithmeticError("control failed")


def c(j,s,t):  # ordinary series of (1+x+t*x*x)^s from F'/F = s Q'/Q
    a=[Q(1)]
    for n in range(1,j+1):
        a.append(((s-(n-1))*a[n-1]+(2*s-(n-2))*t*(a[n-2] if n>=2 else 0))/n)
    return a[j]


def phi(s,b):
    return (s-2)*(s-3)+12*b*(s-2)+12*b*b


# Identities are polynomials over Q: sample more distinct points in each
# coordinate than its degree. No random/singular divisions.
grid=list(map(Q,range(-8,9)))
for s,b in product(grid,repeat=2):
    need(c(2,s,b)==s*(b+(s-1)/2))
    need(c(3,s,b)==s*(s-1)*(b+(s-2)/6))
    need(24*c(4,s,b)==s*(s-1)*phi(s,b))
    need(phi(s,b)==s*s-(5-12*b)*s+6-24*b+12*b*b)
for s,t,b in product(grid,repeat=3):
    num=c(2,s,b)*c(3,t,b)-c(2,t,b)*c(3,s,b)
    e1,e2=s+t,s*t
    need(12*num==-s*t*(s-t)*(12*b*b+2*b*e1-6*b+e2-e1+1))
for b in grid:
    u,v=5-12*b,6-24*b+12*b*b
    need(-(12*b*b+2*b*u-6*b+v-u+1)/12==(4*b-1)/6)
for s in (Q(1,2),Q(3,2)): need(phi(s,Q(1,4))==0)
need(c(3,Q(1,2),Q(1,4))==0)
need([n for n in range(5) if (n+1)<=n*(n+1)//2]==[2,3,4])
print("PASS: 289 binomial/Vieta cases, 4913 alternating identities, 17 symmetric reductions; boundary jets and middle counts exact")
