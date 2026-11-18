"""Exact checks in the algebra of two arbitrary projective measurements.
Relations only: orthogonality/idempotence within each measurement, sum I."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations

def check(ok,msg):
    if not ok: raise ArithmeticError(msg)
I={():1}
def mix(*items):
    d=defaultdict(int)
    for c,A in items:
        for w,v in A.items():d[w]+=c*v
    return {w:v for w,v in d.items() if v}
def times(A,B):
    d=defaultdict(int)
    for w,v in A.items():
        for t,s in B.items():
            if w and t and (w[-1]>0)==(t[0]>0):
                if w[-1]!=t[0]:continue
                word=w+t[1:]
            else:word=w+t
            d[word]+=v*s
    return {w:v for w,v in d.items() if v}
def prod(A,B,C):return times(times(A,B),C)
def fam(n,sg):
    p=[{(sg*i,):1} for i in range(1,n)]
    return p+[mix((1,I),*((-1,P) for P in p))]
def test(n):
    P,Q=fam(n,1),fam(n,-1)
    def gram(k,l):
        return F(1) if k==l else F(-1,n-1)
    def environment_K(i,A,X):
        c=F(n-1,n*(n-2))
        return mix(*[(c*(gram(k,l)-gram(k,i)*gram(i,l)),prod(A[k],X,A[l]))
                     for k in range(n) for l in range(n)
                     if k!=i and l!=i])
    def kraus(i,A,X):
        diff=[mix((1,A[k]),(-1,A[l])) for k,l in combinations(range(n),2) if i not in (k,l)]
        return mix(*[(F(1,(n-1)*(n-2)),prod(D,X,D)) for D in diff])
    sums=[[{} for i in range(n)] for _ in range(6)]
    for i,p in enumerate(P):
        for j,q in enumerate(Q):
            U=mix((1,p),(1,q),(n,prod(p,q,p)),(n,prod(q,p,q)))
            V=mix((2,times(p,q)),(2,times(q,p)))
            k=environment_K(i,P,q);ell=environment_K(j,Q,p)
            check(k==kraus(i,P,q) and ell==kraus(j,Q,p),'K instruments')
            H=mix((F(1,2),k),(F(1,2),ell))
            for ix,A in enumerate((U,V,H)):
                sums[ix][i]=mix((1,sums[ix][i]),(1,A))
                sums[ix+3][j]=mix((1,sums[ix+3][j]),(1,A))
    for side,meas in enumerate((P,Q)):
        U,V,H=sums[3*side:3*side+3]
        check(mix(*[(1,x) for x in H])==I,'noise total')
        for i,p in enumerate(meas):
            check(V[i]==mix((4,p)),'radical coordinate')
            check(U[i]==mix((2*(n+1),p),(2*(n-1),H[i])),'rational coordinate')
    return 2*n*n
if __name__=='__main__':
    ct=0
    for n in range(3,8):
        ct+=test(n);print('universal noncommutative identities checked for equal outcome count',n)
    print('exact one-sided cells tested:',ct,'; both parent marginals checked on both sides.')
