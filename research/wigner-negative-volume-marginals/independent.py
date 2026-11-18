"""Independent exact finite checks, no imports or state from author's script. Proof is analytic."""
from math import comb, factorial
from fractions import Fraction as Q

def require(flag, label):
    if not flag: raise ValueError('FAILED: '+label)

m=64
n=2**m
f=factorial(m)
den=n*n*(n*f-1)**2
a=Q(1,n*f)
r=Q(1,2)
b=[comb(m,j) for j in range(m+1)]
d=[f*bi-(j==0) for j,bi in enumerate(b)]
u=[(n if j==0 else 0)-bi for j,bi in enumerate(b)]
# q_ij numerator times the positive common denominator; it is integer.
joint=[[n*n*di*dj-4*ui*uj for (dj,uj) in zip(d,u)] for (di,ui) in zip(d,u)]
require(min(map(min,joint))>0 and sum(map(sum,joint))==den, 'positive trace-one two-mode state')
require(all(sum(row)==di*n*n*(n*f-1) for row,di in zip(joint,d)), 'first marginal')
require(all(sum(row)==di*n*n*(n*f-1) for row,di in zip(zip(*joint),d)), 'second marginal')
require(joint[0][0]!=n*n*d[0]**2,'non-product diagonal')
print('PASS: 4,225 exact integer matrix entries, trace, two marginals, nonproduct')

# V_j(t)=j!(-1)^j L_j(2t): independent three-term recurrence over Z[t].
polys=[(1,)]
for j in range(m):
    T=polys[j]; B=(0,) if j==0 else polys[j-1]
    Tnew=[0]*(j+2)
    for k,val in enumerate(T):
        Tnew[k]-=(2*j+1)*val
        Tnew[k+1]+=2*val
    for k,val in enumerate(B): Tnew[k]-=j*j*val
    polys.append(tuple(Tnew))
require(all(sum(coef*factorial(k) for k,coef in enumerate(P))==factorial(j) for j,P in enumerate(polys)), 'radial normalized Fock basis')
# Integer coefficients of n*m! times mixture W after removing common vacuum.
C=[0]*(m+1)
for j,(bj,P) in enumerate(zip(b,polys)):
    for k,val in enumerate(P): C[k]+=bj*(f//factorial(j))*val
require(C==[0]*m+[n], 'binomial state monomial symbol')
print('PASS: all 65 radial basis integrals and all 65 mixture coefficients by recurrence')

# Interval/rational steps of an independent continuous-region bound from REVIEW.md.
require(a<Q(1,16) and 4*(1-a)**2>3,'negative square pointwise bound')
alpha=Q(1,2)-Q(1,m)
require(Q(2,1)/(alpha*(1+alpha))<3,'outer half of independent I_m bound')
require(8*7**2 < 512, 'alternative upper-quadrant constant')
require(32*a/r<Q(1,8), 'two mixed strips')
require(-Q(1,2)+Q(392,m*m)+Q(1,8) < -Q(1,4),'strict integrated certified deficit')
print('PASS: independent area envelope I_m<7/m; normalized deficit is strictly below -1/4')
