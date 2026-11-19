"""Exact finite sanity checks, not a proof by extrapolation. Standard library only."""
from fractions import Fraction as F
from itertools import product, permutations
from collections import Counter
from math import comb, gcd, prod
from functools import reduce

def check(x, msg):
    if not x: raise ValueError(msg)

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def reduce_row(a):
    z=reduce(gcd,(abs(x) for x in a),0)
    if not z: return ()
    return tuple(x//z for x in a)

def proj(x,y): # projective representative, positive scalar normalization
    aa,ab=dot(y,y),dot(x,y)
    return reduce_row([a*aa-b*ab for a,b in zip(x,y)]) or x

def upd(V,s,t):
    W=list(V); W[t]=proj(V[t],V[s])
    return tuple(W)

def terminal(V): return all(proj(x,y)==x for x in V for y in V)
def sweep(V):
    for i,x in enumerate(V):
        for j in range(i+1,len(V)): V=upd(V,i,j)
    return V

def rank(A):
    rows=[list(map(F,r)) for r in A]; h=0
    for j in range(len(rows[0])):
        k=next((k for k in range(h,len(rows)) if rows[k][j]),None)
        if k is None:continue
        rows[h],rows[k]=rows[k],rows[h]; z=rows[h][j]
        for i in range(h+1,len(rows)):
            w=rows[i][j]/z
            rows[i]=[a-w*b for a,b in zip(rows[i],rows[h])]
        h+=1
    return h

def determinant(A):
    if len(A)==0:return 1
    return sum((-1)**j*a*determinant([r[:j]+r[j+1:] for r in A[1:]]) for j,a in enumerate(A[0]))

def delta(V):
    B=[[dot(x,y) for y in V] for x in V];n=len(V)
    d=determinant(B)
    g=sum(F(B[i][i]*determinant([r[:i]+r[i+1:] for j,r in enumerate(B) if i!=j]),d) for i in range(n))-n
    return F(d,prod(B[j][j] for j in range(n))),g

rows=[(1,0,0),(-1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,1,1),(1,-1,1)]
ncase=0
for V in product(rows,repeat=4):
    W=sweep(V)
    check(terminal(W) and rank(W)==rank(V),"sweep failure")
    ncase+=1
print('triangular sweep and preserved rank:',ncase,'exact 4-row inputs')

gc=0
for V in product(rows,repeat=3):
    if rank(V)!=3:continue
    vol,g=delta(V); val=0
    for s,t in permutations(range(3),2):
        v0,g0=delta(upd(V,s,t));check(v0>=vol,"decrease")
        val+=g0
    check(val==4*g,"potential expectation");gc+=1
print('inverse-Gram contraction:',gc,'full-rank test inputs, both orientations')

# Exact Markov count of all words and compare the two-coupon CDF.
a=((1,0,0,0),(3,4,0,0),(0,0,1,0),(0,0,3,4))
q=Counter({a:1});T=11
for t in range(T+1):
    done=sum(w for V,w in q.items() if delta(V)[0]>=F(9,10)**2)
    check(done==12**t-2*10**t+8**t,"coupon CDF")
    q2=Counter()
    for V,w in q.items():
        for i,j in permutations(range(4),2):q2[upd(V,i,j)]+=w
    q=q2
print('rational block determinant threshold: exact CDF matches all ordered histories through step',T)

# Projection on rational planar lines, plus reverse pure-death distribution.
def cross(v):
    x,y=v
    return min(tuple(z) for z in [(x,y),(-x,-y),(-y,x),(y,-x)])
rows2=[(1,0),(0,-1),(1,1),(-1,1),(2,1),(1,-2),(-1,-2)]
for x,y in product(rows2,repeat=2):check(cross(proj(x,y))==cross(y),'projective label')
m=4; ar=m*(m-1); initial=tuple(range(m)); mct=Counter({initial:1}); co={m:1}
for t in range(10):
    check(sum(w for V,w in mct.items() if len(set(V))==1)==co.get(1,0),'lineage CDF')
    mprev=mct; mct=Counter()
    for V,w in mprev.items():
        for s,k in permutations(range(m),2):
            W=list(V);W[k]=V[s];mct[tuple(W)]+=w
    aux=Counter()
    for k,w in co.items():
        aux[k]+=w*(ar-k*(k-1))
        if k>1:aux[k-1]+=w*k*(k-1)
    co=aux
check(sum(F(ar,k*(k-1)) for k in range(2,m+1))==(m-1)**2,'mean consensus time')
print('planar quotient:',len(rows2)**2,'exact ordered pairs; 10 exact voter/lineage CDF comparisons')
