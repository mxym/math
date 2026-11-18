"""Second, independent pure integer/rational certificate. Run with Python >=3.8.
No Taylor series: (1-x/m)^m <= exp(-x) <= (1+x/m)^(-m).
Uses F'' on the left and F' on the right, not positivity sampled on middle cells.
"""
from fractions import Fraction as Q
from math import isqrt
from functools import lru_cache

B = 10**7
def ck(x, why):
    if not x: raise ArithmeticError(why)

def down(x): return Q((B*x).__floor__(), B)
def up(x): return Q((B*x).__ceil__(), B)
def sqrt_bracket(x):
    ck(x>=0,'sqrt domain')
    i=isqrt((x*B**2).__floor__()); a=Q(i,B)
    return a, a if a*a == x else Q(i+1,B)
@lru_cache(None)
def exp_bracket(x):
    # Range reduction: x = 1024 y; 1-y <= e^-y <= (1+y)^-1.
    ck(0<=x<=1, 'exponential domain')
    m=1024
    # Repeated interval squaring from crude linear reciprocal bounds, with
    # directed rational rounding only, avoids large numerators.
    lo,hi=1-x/m,1/(1+x/m)
    for j in range(10): lo,hi=down(lo*lo),up(hi*hi)
    return lo,hi

def expneg(lo, hi):
    ck(lo<=hi, 'empty argument')
    return exp_bracket(hi)[0],exp_bracket(lo)[1]

s0,s1=Q(46019,100000),Q(46020,100000)
def Hderivs(l,u):
    rl=sqrt_bracket(1+l*l)[0]; ru=sqrt_bracket(1+u*u)[1]
    A,B=expneg(s0*l,s1*u); C,D=expneg(s0*rl,s1*ru)
    # H'= -s*a + c/r^3 - s*c*u^2/r^2.
    m1=-s1*B+C/ru**3-s1*D*(u/rl)**2
    M1=-s0*A+D/rl**3-s0*C*(l/ru)**2
    # H''=s^2*a + c(s^2*u^3/r^3 - 3*u/r^5 - 3*s*u/r^4)
    m2=s0**2*A+C*s0**2*(l/ru)**3-3*D*u/rl**5-3*s1*D*u/rl**4
    M2=s1**2*B+D*s1**2*(u/rl)**3-3*C*l/ru**5-3*s0*C*l/ru**4
    return m1,M1,m2,M2

def root_test():
    # Extra precision is needed for root signs. Different enclosure from the
    # Taylor proof: alternating convex log bounds, using one small (rational)
    # argument and 20 exact powers of two with directed 16-decimal rounding.
    b=10**16; m=2**20
    def coarse(x):
        lo,hi=1-x/m,1/(1+x/m)
        for j in range(20):
            lo=Q((b*lo**2).__floor__(),b)
            hi=Q((b*hi**2).__ceil__(),b)
        return lo,hi
    rootlo=Q(isqrt(2*b*b),b); roothi=rootlo+Q(1,b)
    y=coarse(s0)[0]+coarse(s0*roothi)[0]/roothi-1
    z=coarse(s1)[1]+coarse(s1*rootlo)[1]/rootlo-1
    ck(y>0 and z<0,'root enclosure')
    return (10**8*y).__floor__(), (10**8*z).__ceil__()

def main():
    print("Root bracket signs, lower and upper in 1e-8:",*root_test())
    # On [0,1/4], F''(t)=H''(1-t)-H''(t); on [1/4,1/2],
    # F'(t)=-H'(1-t)-H'(t). Test genuine closed intervals.
    n=512
    u2=[];u1=[]
    for i in range(n//2):
        t0,t1=Q(i,n),Q(i+1,n)
        p=Hderivs(t0,t1);q=Hderivs(1-t1,1-t0)
        if t1<=Q(1,4): u2.append(q[3]-p[2])
        else: u1.append(-p[0]-q[0])
    ck(len(u2)==128 and len(u1)==128,'cover')
    ck(max(u2)<-Q(1,20),('left not concave',max(u2)))
    ck(max(u1)<-Q(1,200),('right not decreasing',max(u1)))
    print("Negative upper bound for F'' on [0,1/4], times 1e6:",(10**6*max(u2)).__ceil__())
    print("Negative upper bound for F' on [1/4,1/2], times 1e6:",(10**6*max(u1)).__ceil__())
    print("PASS 128 concave cells + 128 decreasing cells, throughout closed root bracket.")
if __name__=='__main__': main()
