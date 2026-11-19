"""Independent exact fixed-anchor chord/triangle integration for the true perimeter ellipse."""
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
from collections import defaultdict
import sympy as s
N=4
I=s.I
pi=s.pi
def req(a,msg):
    if not a: raise ArithmeticError(msg)

# Fourier coefficients of w(x)=sqrt(1-rho cos 2x)/mean(sqrt(...)).
def choose_half(n):
    v=Q(1)
    for k in range(n):v=v*(Q(1,2)-k)/(k+1)
    return v

def coeff(j,k):
    if abs(k)>j or (j-k)%2: return 0
    return choose_half(j)*(-1)**j*comb(j,(j-k)//2)*Q(1,2**j)
cw={}
for j in range(N+1):
    for k in range(-j,j+1):
        cw[j,k]=coeff(j,k)-sum(coeff(r,0)*cw.get((j-r,k),0) for r in range(1,j+1))

# beta(m)=sum rho^n sin(2nm)/n, so orthogonality gives coefficients
# of average(e^(2i M m) beta(m)^r) without numerical quadrature.
B={(0,0,0):s.S.One}
for r in range(1,N+1):
    for n in range(r,N+1):
        for k in range(-n,n+1):
            B[r,n,k]=sum((B.get((r-1,n-a,k-a),0)-B.get((r-1,n-a,k+a),0))/(2*I*a) for a in range(1,n+1))

L=s.symbols('L', real=True)
def E(a): return s.exp(2*I*a*L)
def ip(a): return (E(a)-1)/(2*I*a) if a else L

def tri(a,b):
    if b: return (E(b)*ip(a-b)-ip(a))/(2*I*b)
    if a: return (E(a)-1)/(2*I*a)**2-L/(2*I*a)
    return L*L/2

def main():
    sample=defaultdict(int)
    # Group all coefficients of the product of three weights before integrating.
    for n1,n2,n3 in product(range(N+1),repeat=3):
        degree=n1+n2+n3
        if degree>N:continue
        for j,k,l in product(range(-n1,n1+1),range(-n2,n2+1),range(-n3,n3+1)):
            q=cw[n1,j]*cw[n2,k]*cw[n3,l]
            if q: sample[degree,j+k+l,-j+k+l,2*l]+=q
    out=[s.S.Zero]*(N+1)
    for (degree,M,a,b),q in sample.items():
        if not q: continue
        F=tri(a,b)
        for r in range(N+1-degree):
            # e^(2i b beta) F(pi/2-beta) coefficient at beta^r.
            cr=sum((2*I*b)**(r-i)*(-1)**i*s.diff(F,L,i).subs(L,pi/2)/(factorial(i)*factorial(r-i)) for i in range(r+1))
            for p in range(r,N+1-degree):
                out[degree+p]+=s.Rational(q.numerator,q.denominator)*cr*B.get((r,p,-M),0)
    out=[s.simplify(x) for x in out]
    req(out==[pi**2/8,0,0,0,s.Rational(37,96)],out)
    print('Fixed-anchor triangle integrals through order four:',out)
    print('Acute probability coefficients:', [s.simplify((1 if n==0 else 0)-6*x/pi**2) for n,x in enumerate(out)])
    print('PASS (independent necessary-boundary parameterization, no endpoint clipping).')
if __name__=='__main__': main()
