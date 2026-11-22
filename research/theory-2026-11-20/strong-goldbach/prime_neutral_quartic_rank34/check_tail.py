"""Exact quadratures, adapted from repository check_quadratic.py."""
from fractions import Fraction as F
from math import factorial
def need(b):
    if not b: raise ArithmeticError("failed bound")
def ceil(x): return -(-x.numerator//x.denominator)
def up(x,d=10**16): return F(ceil(x*d),d)
def dn(x,d=10**16): return -up(-x,d)
def alog(x):
    t=(x-1)/(x+1)
    need(0<=t<=F(1,3))
    q=sum((t**(2*j+1)/(2*j+1) for j in range(16)),F())
    return dn(2*q),up(2*(q+t**33/(33*(1-t*t))))
LL,LU=alog(F(2))
def logup(x):
    p=x.numerator.bit_length()-x.denominator.bit_length()
    if F(2)**p>x: p-=1
    return p*LU+alog(x/F(2)**p)[1]
piL,piU=F(3141592653589,10**12),F(3141592653590,10**12)
def atan_small(x):
    need(abs(x)<=F(1,2))
    t=sum(((-1)**i*x**(2*i+1)/(2*i+1) for i in range(24)),F())
    e=x**49/49
    return dn(min(t,t+e)),up(max(t,t+e))
aL,aU=atan_small(F(1,5))
bL,bU=atan_small(F(1,239))
need(piL<16*aL-4*bU<16*aU-4*bL<piU)
def atanup(x):
    if x<=F(1,2):return atan_small(x)[1]
    if x>=2:return piU/2-atan_small(1/x)[0]
    return piU/4+atan_small((x-1)/(x+1))[1]
C=(4/piL)*(sum((logup(F(i))/(4*i*i-1) for i in range(2,11)),F())+(logup(F(10))+1)/(10*(4-F(1,121))))
need(C<F(31,100))
def R(r,z):
    z=up(z,10**10)
    m=10**15
    a=ceil(m*z**r/factorial(r))
    tot=a
    for j in range(r,81,2):
        a=ceil(a*z*z/((j+1)*(j+2)))
        tot+=a
    need(z*z/(82*83)<F(1,2))
    return F(tot+a,m)
def mesh(l,h,m):
    for e in range(l,h):
        for j in range(m):
            yield F(2)**e*F(m+j,m),F(2)**e*F(m+j+1,m)
Q,T=F(),F()
for lo,hi in mesh(-1,24,256):
    z=min(hi,2*logup(1+hi*hi)/piL+2*C)
    a=(lo**-2-hi**-2)/2
    b=(lo**-4-hi**-4)/4
    Q+=up(4/piL*a*R(11,z))
    T+=up(64/piL*b*R(9,z))
# At low t, R_r <=2t^r/r!, and at high t R_r<= exp(z)/2 <= t^(4/3).
Q+=8/piL*F(1,2)**9/(9*factorial(11))+2*F(2)**-16
T+=128/piL*F(1,2)**5/(5*factorial(9))+8*F(2)**-64
need(Q<F(201,10000))
need(T<F(163,100000))
U=F()
for lo,hi in mesh(-16,18,512):
    z=min(hi,2*atanup(hi/2))
    U+=up(64/piL*(lo**-4-hi**-4)/4*z**5/factorial(5))
U+=64/piL*F(2)**-16/factorial(5)
U+=64/piL*piU**5*F(2)**-72/(4*factorial(5))
need(U<F(2918,10000))
# -I_5(A2)<.142816 through the cited, exact quadratic formula.
semi=F(2,3)
high0=F(142816,10**6)
fourier=semi+high0+U+Q+T
total=fourier+F(1661+1824,100000)
need(F(3446,1000)*total<F(997,250))
print(f"ordinary angular upper constants: A4 rank 5 {float(U):.10f}; -A2 odd >=11 {float(Q):.10f}; |A4| odd >=9 {float(T):.10f}")
print(f"true unwanted upper < {float(F(3446,1000)*total):.10f} M")
