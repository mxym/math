"""Exact exhaustive check using Prüfer sequences and literal subset enumeration.
Reads no author file. Run python3 -B -O independent.py.
"""
from collections import Counter
from fractions import Fraction as F
from heapq import heapify, heappop, heappush
from itertools import product
from math import comb,prod

def req(condition,context):
    if not condition: raise AssertionError(context)
def C(n,k):return comb(n,k) if 0<=k<=n else 0
def excess(w,n):return tuple(w.count(j) for j in range(n))
def labeled(w,n,hist):
    deg=[x+1 for x in hist];leaves=[i for i in range(n) if deg[i]==1];heapify(leaves)
    edges=[]
    for u in w:
        x=heappop(leaves);edges.append((1<<u)|(1<<x));deg[u]-=1
        if deg[u]==1:heappush(leaves,u)
    edges.append(sum(1<<x for x in leaves));return edges
def test():
    total=nj=nm=ndp=0
    for n in range(2,8):
        bits=range(1<<n);pop=[x.bit_count() for x in bits]
        patterns=[(k,r,(1<<r)-1|(((1<<(k-r))-1)<<k)) for k in range(1,n) for r in range(max(0,2*k-n),k+1)]
        sums=Counter();joints=Counter();coeffs=[Counter() for _ in range(n)]
        for w in product(range(n),repeat=n-2):
            total+=1;h=excess(w,n);W=sum(C(y,2) for y in h);edges=labeled(w,n,h)
            ok=[all(b&e!=e for e in edges) for b in bits]
            X=Counter(pop[b] for b in bits if ok[b])
            for k in range(1,n):
                x=X[k]
                sums[k,0]+=x;sums[k,1]+=x*x;sums[k,2]+=x*W;sums[k,3]+=x*W*W
                if ok[(1<<k)-1]:coeffs[k][h]+=1
            for k,r,v in patterns:
                if ok[(1<<k)-1] and ok[v]:joints[k,r]+=1
        t=n**(n-2)
        for k in range(1,n):
            m=n-k;b=k-1;u=m-1;rho=F(m,n)**(k-1);X=C(n,k)*rho
            req(F(sums[k,0],t)==X,('first',n,k))
            D=F(n-k+1)
            if C(n-k+1,k):
                er=prod(1+F(k*j,n*(n-k-j)) for j in range(k-1))
                req(X/C(n-k+1,k)==er,('path',n,k))
            theta=F(k*k,n);M2=F(0)
            for kk,r,v in patterns:
                if kk!=k:continue
                M=F(n-r,n)*(1+(r-theta)/(n*(1-F(k,n))**2))**r
                req(F(joints[k,r],t)==M*rho**2,('joint',n,k,r))
                mass=F(C(k,r)*C(n-k,k-r),C(n,k));M2+=mass*M;nj+=1
            req(F(sums[k,1],t)/X**2==M2,('second',n,k))
            mean=F(C(n-2,2),n)+C(b,2)*(F(1,m)-F(1,n))
            var=(C(u,2)+u*b)*F(n-1,n**2)+C(b,2)*F(m-1,m**2)+F(u*b*(b-1)*k,n**2*m)
            req(F(sums[k,2],sums[k,0])==mean,('planted mean',n,k))
            req(F(sums[k,3],sums[k,0])==var+mean**2,('planted var',n,k));nm+=1
            # Check the full multivariate weighted-tree polynomial by degree vector,
            # not by sampling a finite set of evaluations.
            alt=Counter()
            for a in product(range(k,n),repeat=b):
                for c in product(range(n),repeat=u):alt[excess(a+c,n)]+=1
            req(alt==coeffs[k],('planted degree polynomial',n,k));ndp+=len(alt)
    print('All labeled trees n=2..7:',total,'nontrivial coefficient sizes:',nm)
    print('Exact pair probabilities by admissible overlap:',nj,'full planted degree polynomial nonzero monomials:',ndp)
    print('Exact first/second moments, finite path ratio and all planted collision means/variances (including m=1): PASS')
if __name__=='__main__':test()
