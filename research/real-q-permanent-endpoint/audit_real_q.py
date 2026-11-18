#!/usr/bin/env python3
"""Independent finite diagnostics, not numerical evaluation of the huge witness."""
from collections import defaultdict
from fractions import Fraction as R
from itertools import permutations, combinations
from math import prod, factorial, comb
from random import Random

def req(x, msg):
    if not x: raise ArithmeticError(msg)

def coords(rows,d):
    X = {(0,)*d: 1}
    for row in rows:
        Z = defaultdict(int)
        for k, val in X.items():
            for a,r in enumerate(row):
                h=list(k);h[a]+=1;Z[tuple(h)] += val*r
        X=Z
    return X

def norm(X):
    return sum(v*v*prod(map(factorial,k)) for k,v in X.items())

def test(V):
    d=len(V[0]);n=len(V)
    H=[[sum(a*b for a,b in zip(v,w)) for v in V] for w in V]
    perm=der=0
    for s in permutations(range(n)):
        term=prod(H[i][j] for i,j in enumerate(s))
        perm+=term;der+=term*sum(s[i]>s[j] for i,j in combinations(range(n),2))
    req(perm==norm(coords(V,d)), 'Fischer/permanent')
    F={(a,b):defaultdict(int) for a,b in combinations(range(d),2)}
    for i,j in combinations(range(n),2):
        X=coords([v for h,v in enumerate(V) if h!=i and h!=j],d)
        for (a,b),pol in F.items():
            det=V[i][a]*V[j][b]-V[i][b]*V[j][a]
            for k,v in X.items():pol[k] += det*v
    req(comb(n,2)*perm-2*der == sum(map(norm,F.values())), 'endpoint identity')
    return der

rng=Random(68831)
cases=0
for n in range(2,8):
    for d in range(2,5):
        V=[[rng.randrange(-4,5) for _ in range(d)] for _ in range(n)]
        if n>3 and d<4: V[-1]=V[0][:]
        for sel in [V,V[1::2]+V[::2]]:
            test(sel);cases+=1
print('Direct permutation vs coefficient-Fischer identity:',cases,'small ordered examples in real ranks <=4.')

# Pair-order identity including multiple exact ties and negative coordinates.
Y=[R(x,7) for x in sorted([2,0,-10,-1,1,99,0,0,-20,0,8,20,0])]
n=len(Y)
req(sum((2*i+1-n)*y for i,y in enumerate(Y))==sum(abs(a-b) for a,b in combinations(Y,2)), 'sorted Gini')

# Exact integer multiplicities, no construction of Q or row list.
M=10**22; Z=prod(10000+j*j for j in range(10001));D=100*Z
n=D*M*M
F=lambda j:R(j*j,10000+j*j)
counts=0
for j in range(10001):
    b=(F(j+1)-F(j)) if j<10000 else (1-F(j))
    c=D*(R(99,100)*b+R(int(j==0),100))
    req(c.denominator==1 and c>=0,'multiplicity')
    counts += c.numerator
req(counts==D,'multiplicities must sum exactly')
# Digit estimate by rational approximation to log_10(2); then exact bracket.
e=n.bit_length()*30103//100000
while n<10**e:e-=1
while n>=10**(e+1):e+=1
req(10**e<=n<10**(e+1),'digit bracket')
print('All 10001 exact radial probabilities sum to 1 and yield integer row multiplicities.')
print('Explicit order n has', e+1, 'decimal digits; its bit length is',n.bit_length())

# Replace infeasible 2/Q by a deliberately loose upper bound; non-materialized
# telescoping error 4M*3^(M-1)*10^(-2M)<=4M*10^(-M-1)<=1 for every M>=1.
delta=R(1,10**60)
rho0=R(1,10**8);rho1=R(1,10**22)
pi_lo=R(314,100);pi_hi=R(22,7); log3_hi=R(11,10);isqrt2_hi=R(10,7)
req(2*log3_hi/M-rho0*rho0/200 < -R(4,10**19),'outside potential gap')
req(delta+isqrt2_hi*102*rho1<R(2,10**20),'inside factor')
req((rho1/2)**6>R(1,10**138),'sphere tube')
# log(10)<3; use it at both 138 and 2 powers of ten.
req(2*M*M*(R(4,10**19)-R(4,10**20))>140*3,'probability tilt')
err=pi_hi/200+R(1,100)+R(2,100)+100*(2*pi_hi/M+delta)
req(err<R(46,1000) and pi_lo/4-R(46,1000)>=R(739,1000),'ordering gain')
req((R(70,100))**2 < (1-delta)**2/2,'center denominator')
req(R(70,100)-102*rho0>R(69,100),'tube denominator')
req(R(102**2)*rho0/(R(69,100)*R(70,100))<R(1,1000),'uniform ratio error')
req(R(99,100)*R(73,100)**2 > (1+R(3,1000))*(1+R(2,1000))/2,'threshold for n>=1000')
print('All finite grid, tube, concentration, quotient and derivative thresholds pass exact rational slack checks.')
