"""Exact arithmetic checks of the four displayed disk/square inequalities and an edge Jacobian."""
from fractions import Fraction as F
from itertools import permutations
from math import factorial

def check(q, msg):
    if not q:
        raise ArithmeticError(msg)

def atan_bounds(q, n):
    s=sum(((-1)**j)*q**(2*j+1)/(2*j+1) for j in range(n))
    other=s+(-1)**n*q**(2*n+1)/(2*n+1)
    return min(s,other), max(s,other)

def main():
    a,b=atan_bounds(F(1,5),6)
    c,d=atan_bounds(F(1,239),3)
    L,U=16*a-4*d,16*b-4*c # Machin's pi formula
    check(F(3141,1000)<L<=U<F(22,7),"pi bracket")
    target=F(13,100)
    check(6*L**2*target**2>1, "1−1/(pi√6) > .87")
    check(2*L**3*target**2>1,"1−1/√(2pi³) > .87")
    check(1-F(1,16)+1/(96*L)<F(941,1000), "square upper")
    cut=16*(1+F(1,192)-F(941,1000))
    check(cut>0 and L/2>cut**2,"disk upper")
    for n in (3,5,11,23):
        # Determinant of derivative (x,v)->(left,right), with v *not* identified modulo ±.
        m=[[int(j==i%2) if j<2 else ((-1 if i<2 else 1)*F(int(j-2==i%2),2*n)) for j in range(4)] for i in range(4)]
        val=0
        for p in permutations(range(4)):
            s=(-1)**sum(p[i]>p[j] for j in range(4) for i in range(j))
            for i in range(4): s*=m[i][p[i]]
            val+=s
        check(abs(val)==F(1,n*n),"Jacobian")
        for t in range(1,n//2+1):
            count=1
            for j in range(t):
                count*=((n-2*j)*(n-2*j-1))//2
            check(count==factorial(n)//(factorial(n-2*t)*2**t),"unsigned disjoint ordered edges")
    print("PASS: four disk/square bounds, pi bracket, edge Jacobians and unordered-edge factors (exact arithmetic).")
    print("These are normalization and consequence checks, not a computation of the limiting distribution.")
if __name__=="__main__": main()
