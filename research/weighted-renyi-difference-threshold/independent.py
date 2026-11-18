"""Independent exact arithmetic. Python >=3.8 (standard library); no author imports."""
from fractions import Fraction as F
from itertools import product
from math import prod
def need(ok,s):
    if not ok:raise ArithmeticError(s)
# 1D tilted joint density is p exp(-x-y+(1-p)*[signed excess]/[corresponding scale]).
# Integrate over y below and above lambda*x/mu, leaving H exp(-p*x)+K exp(-x/mu).
def density_coeffs(p,L):
    m=1-L
    rate=1+(1-p)*m/L
    H=p/rate;K=1-H
    need(p+rate*L/m==1/m,'matching exponent at the cutoff')
    need(1+(1-p)*L/m+p*L/m==1/m,'tail exponent')
    need(H/p+K*m==1,'normalized marginal density')
    return H,K
def tilted_mgf(p,L,s):
    H,K=density_coeffs(p,L)
    return H/(p-s)+K/(1/(1-L)-s)
def cubic(p,L,n):
    m=1-L;A=L/(1-m*p);B=m/(1-L*p)
    supp={};high=(1/p,)*n
    for q,b in ((A,m),(B,L)):
        for bits in product((0,1),repeat=n):
            v=tuple(1/p if j else b for j in bits)
            supp[v]=supp.get(v,0)+prod(q if j else 1-q for j in bits)
    need(sum(supp.values())==2 and supp[high]==A**n+B**n,'total / top-atom mass')
    for i in range(n):need(sum(v[i]*w for v,w in supp.items())==1+1/p,'barycenter')
    if supp[high]>=1:
        supp[high]-=1
        need(min(supp.values())>=0 and sum(supp.values())==1,'residual law')
        need(all(sum(w*v[i] for v,w in supp.items())==1 for i in range(n)),'residual mean')
    return
for p,L,n in product((F(1,13),F(1,2),F(4,7),F(11,12)),(F(1,97),F(2,5),F(1,2)),range(1,6)):
    cubic(p,L,n)
    H,K=density_coeffs(p,L);A=L/(1-p*(1-L));need(H/p==A and K*(1-L)==1-A,'mixture weights')
p,L,s,d=F(4,7),F(1,2),F(9,16),F(1,126)
P=(p/(p-s))**2;U=(1/(1-s))**2;Q=tilted_mgf(p,L,s)**2
D=P+U-2*Q
v=s*(1+d)
need(v==F(127,224)<p,'finite error moments')
C=(p/(p-v))**2+(1/(1-v))**2
need((P,U,Q,D,C+P*U)==(4096,F(256,49),F(1081600,529),F(311040,25921),F(17422205952,461041)),'original exact data')
need(1512*d==12,'power of two')
need(D-(C+P*U)/2**12==F(55223727,19909444)>0,'original positivity')
need(D-C/2**12>0,'independent logarithmic bound')
need((p/(1-p))*(D-C/2**12)==F(7802780287,731672067),'independent quantitative J bound')
# For the uniform triangle, HZZZ (58) is the elementary two-power beta integral.
r=12/((2*p+1)*(2*p+2))
need(r==F(98,55) and r**7<4**3,'triangle comparison')
if __name__=='__main__':print('PASS: tilted densities, scale barycenters, original error and logarithmic lower bound:', (p/(1-p))*(D-C/2**12))
