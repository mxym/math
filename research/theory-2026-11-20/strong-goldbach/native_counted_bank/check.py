"""Exact checks for the source, level, polynomial responses, and displayed gap."""
from fractions import Fraction as F
from itertools import combinations
from math import factorial

def check(flag, label):
    if not flag: raise ArithmeticError(label)
v = [F(x,1000) for x in (50,197,229,248,276)]
sub = [(i,sum(w,F(0))) for i in range(6) for w in combinations(v,i)]
A = sum((-1)**k * max(F(0),1-2*t)**2 for k,t in sub)
check(A == -F(19171,125000), 'angular source')
check(min(abs(t-F(1,2)) for _,t in sub)==F(1,200), 'seam distance')
check(-A - F(32*4*5,100000) > F(14,100), 'positive on full finite-width box')
d = F(1,100000)
for t in [v[0]-d, v[0]+d]:
    check(min(F(1,2)+t/2,F(4,7)-F(6,7)*t) > F(5249,10000) > F(516,1000), 'Fouvry rails')
check(F(12,53)-F(3,20)==F(81,1060), 'actual negative zero-population gap')
# Integration of a quadratic after normalized signed averaging is -linear-2s*quadratic.
# Independently represent polynomial coefficients by interpolation at 0,1,2.
def signed(f,s):
    quad=(f(2)-2*f(1)+f(0))/2
    linear=f(1)-f(0)-quad
    return -linear-2*s*quad
def q(x):return (1-2*x)**2
def response(u,marks,s):
    def f(x):
        return sum((-1)**k*q(F(x)+u+sum(z,F(0)))
                   for k in range(len(marks)+1) for z in combinations(marks,k))
    return signed(f,s)
for s in (F(1,49),F(1,5000)):
    for u in (F(0),F(2,17)):
        vv=[F(3,100),F(4,105),F(1,41),F(2,53)]
        check(response(u,[],s)==4-8*u-8*s, 'mass response')
        check(response(u,vv[:1],s)==8*vv[0], 'one mark')
        for k in range(2,5):check(response(u,vv[:k],s)==0,'multiple marks')
        check(signed(lambda x: 1-F(x),s)==1,'linear patch')
# Formal normalized exponential-convolution coefficients through degree 12:
# the shift mean is the first moment, with no higher-order contribution.
for n in range(13):
    mass=sum(F((-1)**(n-j),factorial(j)*factorial(n-j)) for j in range(n+1))
    moment=sum(F(j*(-1)**(n-j),factorial(j)*factorial(n-j)) for j in range(n+1))
    check(mass==(n==0) and moment==(n==1),'normalized exponential coefficients')
print('native-source angular sign, both Fouvry rails, no-mark gap, signed responses, exponential coefficients: PASS')
