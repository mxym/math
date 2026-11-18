#!/usr/bin/env python3
"""Independent exact diagnostics on the actual core and a rectangular test model."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod, comb

def need(x,msg):
    if not x: raise ArithmeticError(msg)

# Bitmasks independently transcribed from OpenAI Table 1 (point 0 is the low bit).
masks=[0xb,0x203,0xd,0x205,0x40a,0x482,0x1082,0x1202,0x1c,0x214,0x818,0xc08,
       0x310,0x910,0xe0,0x860,0x4a0,0xc20,0x10c0,0x940,0x1140,0x1300]
# For two-atom hosts summing the 22 face labels first reduces the other
# integrations to the 2^13 possible assignments of the 13 point labels.
hist=Counter()
for x in range(1<<13):
    c=[0]*4
    for f in masks:c[(f&x).bit_count()]+=1
    hist[x&1,x.bit_count(),*c]+=1
need(sum(hist.values())==8192 and len(hist)==756,'core signatures')
def core(W,pi):
    box=[sum(pi[y]*W[0][y]**(3-k)*W[1][y]**k for y in (0,1)) for k in range(4)]
    boxpowers=[[s**i for i in range(23)] for s in box]
    h=[F(0),F(0)]
    for (root,c,*m),mult in hist.items():
        h[root]+=mult*pi[0]**(13-c)*pi[1]**c*prod(a[b] for a,b in zip(boxpowers,m))
    return [v/p for v,p in zip(h,pi)]

def square(W,pi): # direct weighted codegrees; rectangular handled separately below
    k=[[sum(pi[i]*W[x][i]*W[i][v] for i in range(len(W))) for v in range(len(W))] for x in range(len(W))]
    return [sum(a*v*v for a,v in zip(pi,line)) for line in k]

def stats(W,pi,h):
    d=[sum(a*b for a,b in zip(x,pi)) for x in W];p=sum(a*b for a,b in zip(d,pi))
    c=square(W,pi);Delta=sum(a*x for a,x in zip(pi,c))-p**4
    b=[sum(r*a*g for r,a,g in zip(row,pi,h)) for row in W];n=sum(a*v for a,v in zip(pi,b))
    I=sum(r*v*(s-p**4) for r,v,s in zip(pi,b,c))
    need(Delta>=0 and all(u>=v**143 for u,v in zip(b,c)),'actual core global majorization')
    need(n>=p**299 and sum(a*g for a,g in zip(pi,h))>=p**286,'biclique lower bounds')
    if p>=F(1,4) and Delta<=F(1,2**2706):need(I>=Delta/2**598,'actual local bridge')
    return p,Delta,b,c,n,I
small=[
([[0,F(4,5)],[F(4,5),F(2,5)]],(F(1,2),F(1,2))),
([[F(1,10),F(1,2)],[F(1,2),F(7,8)]],(F(1,3),F(2,3))),
([[0,0],[0,1]],(F(1,6),F(5,6))),
([[F(1,2),F(1,2)],[F(1,2),F(1,2)]],(F(3,4),F(1,4))),
([[1,F(1,2)],[F(1,2),1]],(F(1,2),F(1,2))),
]
for W,pi in small:
    for T in (W,[[1-c for c in r] for r in W]):
        stats(T,pi,core(T,pi))
print('10 exact two-atom tests integrate the actual H without generating all 2^35 assignments.')

# Positive nonconstant Delta smaller than the actual 2^-2706 threshold:
# a rational rank-one host has closed-form vertex moments for the true core.
gap=F(1,2**1400)
a=[F(7,8)-gap,F(7,8)+gap];pi=[F(1,2)]*2
mom=lambda k:sum(p*v**k for p,v in zip(pi,a))
degrees=[sum((f>>i)&1 for f in masks) for i in range(13)]+[3]*22
h=[x**degrees[0]*prod(mom(k) for k in degrees[1:]) for x in a]
p,de,*_=stats([[x*y for y in a] for x in a],pi,h)
need(p>F(3,4) and 0<de<F(1,2**2706),'actual nonconstant near-local test')
print('One nonconstant actual-core local test has p>3/4 and 0<Delta<2^-2706.')

# Nonuniform finite types, independent uniform shared additive group Z/2.
# This example checks only the algebra/factorization, not the rank-layer limit.
A=[(i,z) for i in range(2) for z in range(2)];B=[(j,z) for j in range(3) for z in range(2)]
pi=[(F(1,3),F(2,3))[i]/2 for i,z in A]
nu=[(F(1,5),F(3,10),F(1,2))[j]/2 for j,z in B]
coeff=[[F(1),F(-1,4),F(1,3)],[F(-1),F(2,3),F(-2,5)]]
W=[[1+coeff[i][j]*(-1)**(u^v) for j,v in B] for i,u in A]
def rt(R,pa,pb): # rectangular all pair codegrees and rooted C4s on the row side
    C=[]
    for row in R:
        dots=[sum(v*a*b for v,a,b in zip(pb,row,o)) for o in R]
        need(sum(v*x for v,x in zip(pa,dots))==1,'rooted mean codegree')
        C.append(sum(v*x*x for v,x in zip(pa,dots)))
    return C
cx=rt(W,pi,nu);cy=rt(list(zip(*W)),nu,pi)
need(len(set(cx))>1 and len(set(cy))>1 and min(cx+cy)>=1,'nontrivial rooted square types')
for vec,weights in ((cx,pi),(cy,nu)):
    av=sum(a*c for a,c in zip(weights,vec));margin=av-1
    for j in range(0,len(vec),2):
        need(vec[j]==vec[j+1] and (weights[j]+weights[j+1])*(vec[j]-1)<=margin,'type-to-uniform bound')
XY=list(product(range(len(A)),range(len(B))));mu=[pi[i]*nu[j] for i,j in XY]
V=[[W[i][l]*W[k][j] for k,l in XY] for i,j in XY]
need(all(sum(p*x for p,x in zip(mu,row))==1 for row in V),'product kernel row normalization')
cv=square(V,mu)
need(cv==[cx[i]*cy[j] for i,j in XY],'exact squared-kernel root factorization')
test_h=[F(1+11*i*j,3) for i,j in XY];base=sum(p*h for p,h in zip(mu,test_h))
for e in (1,2,7):
    t=sum(mu[i]*test_h[i]*sum(mu[j]*v*cv[j]**e for j,v in enumerate(row)) for i,row in enumerate(V))
    need(abs(t-base)<=base*max(abs(x**e-1) for x in cv),'uniform control on bridge')
print('Exact rectangular 4-by-6 test: nonconstant rooted types, crossed kernel on 24 atoms, three bridge moments.')
