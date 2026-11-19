"""Regression for the dual fiber-sign encoding; no numerical solver or floating point.
The theorem uses a general QE bound, not experimental extrapolation from these tests.
"""
from fractions import Fraction as F
from itertools import product,combinations
from math import comb
def ck(b,m):
    if not b:raise ArithmeticError(m)
O=(F(0),F(0),F(0));I=(F(1),F(0),F(1))
def scale(c,A):return tuple(c*x for x in A)
def add(A,B):return tuple(x+y for x,y in zip(A,B))
def sub(A,B):return add(A,scale(-1,B))
def total(seq):
    A=O
    for x in seq:A=add(A,x)
    return A
def pairing(A,B):return A[0]*B[0]+2*A[1]*B[1]+A[2]*B[2]
def coefficients(A):return (A[0]+A[2],A[0]*A[2]-A[1]*A[1])
def proj(x,y):return tuple(F(z,x*x+y*y) for z in (x*x,x*y,y*y))
p=[(proj(i,j),proj(-j,i)) for i,j in [(1,0),(1,1),(2,1)]]
# Four three-outcome settings on a real qubit: three different lossy bases and a coin.
eta=F(2,5)
M=[[scale(eta,A) for A in basis]+[scale(1-eta,I)] for basis in p]
M.append([scale(F(1,3),I)]*3)
def feasible_witness(t):
    Fm=[[add(scale(F(1,3),I),sub(scale(t,sub(I,A)),A)) for A in base]+[scale(F(1,3),I)] for base in p]
    Fm.append([O]*3)
    co=[coefficients(total(Fm[i][a] for i,a in enumerate(x))) for x in product(range(3),repeat=4)]
    return Fm,co
t=1
while True:
    Fm,co=feasible_witness(t)
    if all(a>=0 and b>=0 for a,b in co):break
    t*=2
    ck(t<=8192,'unexpected poor margin')
h=sum(pairing(A,B) for mr,fr in zip(M,Fm) for A,B in zip(mr,fr))
ck(h==2-6*eta and h<0,'trace dual target')
faces=nonfaces=0
for sm in range(16):
    S=[i for i in range(4) if sm>>i&1]
    decoded=all(Fm[i][a]==O for i in range(4) if i not in S for a in range(3)) and h<0 and all(a>=0 and b>=0 for a,b in co)
    ck(decoded==(sm&7==7),'one triple witness with extraneous coordinates zero')
    if decoded:
        nonfaces+=1;continue
    faces+=1
    active=[i for i in S if i<3]
    # For each active lossy device sample its projectors with prob eta.
    parent={x:O for x in product(range(3),repeat=len(S))}
    atoms=[(i,a,scale(eta,p[i][a])) for i in active for a in (0,1)]
    atoms.append((-1,-1,scale(1-eta*len(active),I)))
    for i,a,A in atoms:
        for coin in range(3):
            x=tuple((coin if j==3 else (a if j==i else 2)) for j in S)
            parent[x]=add(parent[x],scale(F(1,3),A))
    ck(total(parent.values())==I and all(min(coefficients(A))>=0 for A in parent.values()),'face parent')
    for k,i in enumerate(S):
        for a in range(3):ck(total(A for x,A in parent.items() if x[k]==a)==M[i][a],'marginal')
print('4 three-outcome qubit settings; 14 faces have exact parent matrices, 2 nonfaces share a sign-fiber witness; all 81 PSD coefficient vectors checked.')
print('dual H =',h,'; t =',t)
# Roots and coefficients test for dimensions 1..5 with zero and negative eigenvalues.
cases=0
for d in range(1,6):
    for ev in product(range(-2,3),repeat=d):
        c=[1]
        for z in ev:
            c=[(c[i-1] if i else 0)+(z*c[i] if i<len(c) else 0) for i in range(len(c)+1)]
        ck((min(c)>=0)==(min(ev)>=0),'char coefficient PSD')
        cases+=1
print('all',cases,'integer eigenvalue lists in dimensions 1..5 match the characteristic-coefficient PSD test')
