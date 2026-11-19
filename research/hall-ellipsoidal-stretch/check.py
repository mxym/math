"""Exact sample identities from the analytic proof (not a substitute for it)."""
from fractions import Fraction as Q
from itertools import combinations,product

def need(test):
    if not test: raise ArithmeticError("exact check failed")
def F(x,d):
    z=Q(max(-1,min(1,x)))
    return z/2 if d==3 else (3*z-z**3)/4
def j(a,b,d):
    return (F(a+b,d)+F(a-b,d))/2
def main():
    # Rational points on the unit quarter-circle, including the two endpoints.
    p=[Q(i,8) for i in range(9)]
    cs=[((1-t*t)/(1+t*t),2*t/(1+t*t)) for t in p[::-1]]
    ct=0
    for (a,ab),(b,bb) in combinations(cs,2):
        need(a<b and ab>bb)
        for (c,h),r,v,d in product(cs,(Q(1,2),Q(1),Q(2)),(Q(0),Q(2,3),Q(1)),(3,5)):
            x,y=r*a*c,r*b*c
            n,m=r*ab*h*v,r*bb*h*v
            need(j(y,m,d)>=j(x,m,d)>=j(x,n,d))
            if 0<c<1 and r<=1: need(j(y,m,d)>j(x,n,d))
            ct+=1
    ct2=0
    for spec in product((1,2,3),repeat=3):
        for w in ((1,1,1),(1,2,3),(2,1,0),(0,0,4)):
            moment=lambda k:sum(z*l**k for l,z in zip(spec,w))
            beta=lambda k:Q(moment(k)**2,moment(2*k)*moment(0))
            strict=len({l for l,z in zip(spec,w) if z})>1
            for k in range(4):
                need((beta(k)>beta(k+1)) if strict else beta(k)==beta(k+1))
                ct2+=1
    print(f"PASS: {ct} rational two-point CDF comparisons (d=3,5); {ct2} spectral tilt comparisons")
if __name__=="__main__": main()
