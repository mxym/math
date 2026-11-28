"""Finite checks of the quadratic Fourier and tagged-block lemmas.

Only constant-size synthetic vector spaces are enumerated. There is no
likelihood optimizer or instance interface in the script.
"""
from fractions import Fraction
from itertools import product, combinations
from random import Random

def rank(A,p):
    L=[list(a) for a in A]
    if not L: return 0
    k=0
    for j in range(len(L[0])):
        can=next((i for i in range(k,len(L)) if L[i][j]%p),None)
        if can is None: continue
        L[k],L[can]=L[can],L[k]
        inv=pow(L[k][j]%p,-1,p)
        L[k]=[a*inv%p for a in L[k]]
        for i in range(k+1,len(L)):
            c=L[i][j]
            L[i]=[(a-c*b)%p for a,b in zip(L[i],L[k])]
        k+=1
    return k

def slice_mat(A,I):
    return [[A[i][j] for j in I] for i in I]

rng=Random(82612)
rows=deletions=0
for p,n in ((2,6),(3,4),(5,2)):
    V=tuple(product(range(p),repeat=n))
    pairs=list(combinations(range(n),2))
    for _ in range(25):
        c=rng.randrange(p)
        H=[rng.randrange(p) for _ in pairs]
        K=[rng.randrange(p) for _ in range(n)]
        a=[rng.randrange(p) for _ in range(n)]
        B=[[0]*n for _ in range(n)]
        for i in range(n): B[i][i]=2*K[i]%p
        for v,(i,j) in zip(H,pairs): B[i][j]=B[j][i]=v
        r=rank(B,p)
        J=next(I for I in combinations(range(n),r) if rank(slice_mat(B,I),p)==r)
        for size in range(r+1):
            for H0 in combinations(J,size):
                I=[i for i in range(n) if i not in H0]
                assert rank(slice_mat(B,I),p)>=r-2*size
                deletions+=1
        f=[(c+sum(k*x[i]*x[i]+a[i]*x[i] for i,k in enumerate(K))
                +sum(v*x[i]*x[j] for v,(i,j) in zip(H,pairs)))%p for x in V]
        nonzero=0
        for u in V:
            hh=[0]*p
            for x,z in zip(V,f):
                hh[(z-sum(a*b for a,b in zip(u,x)))%p]+=1
            squares=[sum(hh[k]*hh[(k-t)%p] for k in range(p)) for t in range(p)]
            assert len(set(squares[1:]))==1
            sq=squares[0]-squares[1]
            assert sq in (0,p**(2*n-r))
            nonzero+=sq>0
            rows+=1
        assert nonzero==p**r

# Exact chord/mgf for a finite toy set of tag pools.
mgf_cases=0
for s in range(1,7):
    for blocks in product(range(s+1),repeat=3):
        epsilon=Fraction(1,64)
        M=sum((epsilon**sum(tags))*(1-epsilon)**(3-sum(tags))*
              2**sum(v*t for v,t in zip(blocks,tags))
              for tags in product((0,1),repeat=3))
        bound=Fraction(1)
        for r in blocks:
            assert 2**r-1 <= Fraction(r,s)*(2**s-1)
            bound*=1+epsilon*Fraction(r,s)*(2**s-1)
        assert M<=bound
        mgf_cases+=1

def padd(P,Q,sign=1):
    A=[0]*max(len(P),len(Q))
    for j,a in enumerate(P): A[j]+=a
    for j,b in enumerate(Q): A[j]+=sign*b
    return A

def pmul(P,Q):
    A=[0]*(len(P)+len(Q)-1)
    for i,a in enumerate(P):
        for j,b in enumerate(Q):
            A[i+j]+=a*b
    return A

def ev(P,x):
    A=0
    for a in reversed(P):A=a+x*A
    return A

cheb=0
for m in range(2,21):
    arg=[Fraction(m+1,m-1),Fraction(-2*m,m-1)]
    last=[1]; cur=arg[:]
    for k in range(1,17):
        denom=cur[0]
        assert denom>=1 and sum(abs(x) for x in cur)<=15**k
        P=padd([1],[x/denom for x in cur],-1)
        assert ev(P,0)==0 and sum(abs(x) for x in P)<=1+15**k
        for j in range(1,m+1):
            assert abs(ev(P,Fraction(j,m))-1)*denom<=1
            cheb+=1
        last,cur=cur,padd(pmul([2*a for a in arg],cur),last,-1)

fibers=0
for p in (2,3,5):
    for left in product(range(p),repeat=3):
        for right in product(range(p),repeat=3):
            diffs=tuple((a-b)%p for a,b in zip(left,right))
            h=[0]*p
            for s in product(range(p),repeat=3):
                h[sum(a*b for a,b in zip(diffs,s))%p]+=1
            if left==right:
                assert h==[p**3]+[0]*(p-1)
            else:
                assert h==[p**2]*p
            fibers+=1

print("PASS: Fourier rows, pivot deletion, tag mgf, Chebyshev nodes, intersections:",
      rows,deletions,mgf_cases,cheb,fibers)

from math import comb, factorial

def Aadd(a,b,p):
    return tuple((u+v)%p for u,v in zip(a,b))

def diff(f,x,deltas,p):
    out=0
    for mask in product((0,1),repeat=len(deltas)):
        u=x
        for h,t in zip(deltas,mask):
            if t: u=Aadd(u,h,p)
        out+=(-1)**(len(deltas)-sum(mask))*f(u)
    return out%p

cosets=0
for p in (2,3,5):
    H=((p-1,0,1,0),(0,1,0,1))
    def f(x):
        a,b,c,d=x
        return ((a+c)*b*d+(b-d)*a*c+c*d+a)%p
    for s,t,c,d in product(range(p),repeat=4):
        x=((s-c)%p,(t+d)%p,c,d)
        for h1,h2,h3 in product(H,repeat=3):
            assert diff(f,x,(h1,h2,h3),p)==0
            cosets+=1
    # The degree-three diagonal identity would lose the whole top part in
    # these small characteristics, but there is a nonzero polarization.
    if p in (2,3):
        e=((1,0,0),(0,1,0),(0,0,1))
        g=lambda a:a[0]*a[1]*a[2]%p
        assert diff(g,(0,0,0),e,p)==1 and factorial(3)%p==0

diagonals=0
for p in (5,7):
    for k in range(2,5):
        g=lambda x:(x[0]**k+2*x[0]**(k-1)*x[1])%p
        f=lambda x:(g(x)+x[1]**(k-1)+x[0]+1)%p
        for h in product(range(p),repeat=2):
            val=sum((-1)**(k-j)*comb(k,j)*f(tuple(j*a%p for a in h))
                    for j in range(k+1))
            assert val%p==factorial(k)*g(h)%p
            diagonals+=1

couplings=0
sigma=Fraction(1,10); e=Fraction(1,20)
for s1,s2 in product(range(1,9),repeat=2):
    A=[]
    for s in (s1,s2):
        W=[]
        for mask in product((0,1),repeat=s):
            i=sum(mask); p=sigma**i*(1-sigma)**(s-i)
            tag=Fraction(0) if i else e/(1-sigma)**s
            assert tag<=1 and (not i or tag==0)
            W.append((p*tag,p*(1-tag)))
        A.append(tuple(sum(w[j] for w in W) for j in (0,1)))
    P={(t,s):A[0][t]*A[1][s] for t,s in product((0,1),repeat=2)}
    assert P=={(0,0):e*e,(0,1):e*(1-e),(1,0):(1-e)*e,(1,1):(1-e)**2}
    couplings+=1
print("PASS: cubic coset derivatives, polarization diagonals, block-coin couplings:",
      cosets,diagonals,couplings)
