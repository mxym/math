"""Exact finite checks of the identities and examples; not an asymptotic proof."""
from math import comb, factorial
from itertools import combinations
from fractions import Fraction as F

def need(ok,why):
    if not ok:raise ArithmeticError(why)
def M(j):return j*(j-1)//2
def greedy(n,edges,A):
    parent=list(range(n));out=0
    def root(v):
        while v!=parent[v]:v=parent[v]
        return v
    for i,(x,y) in enumerate(edges):
        if A>>i&1:
            x=root(x);y=root(y)
            if x!=y:parent[x]=y;out|=1<<i
    return out
def exhaustive():
    ng=ns=0
    for n in range(2,6):
        ed=list(combinations(range(n),2));r=n-1
        trees=[greedy(n,ed,A) for A in range(1<<len(ed))]
        for G,Tfull in enumerate(trees):
            if Tfull.bit_count()!=r:continue
            m=G.bit_count();ng+=1
            subs=[];A=G
            while True:
                if trees[A].bit_count()==r:subs.append(A)
                if not A:break
                A=(A-1)&G
            # Compute the direct reliabilty coefficient vector in increasing powers of q
            co=[0]*(m+1)
            for A in subs:
                k=A.bit_count()
                for h in range(k+1):co[m-k+h]+=(-1)**h*comb(k,h)
            hh=[0]*(m-r+1)
            for T in (x for x in subs if x.bit_count()==r):
                forb=0
                for j in range(len(ed)):
                    if (G^T)>>j&1 and greedy(n,ed,T|1<<j)!=T:forb|=(1<<j)
                hh[forb.bit_count()]+=1
                a={x for x in subs if trees[x]==T}
                b={x for x in subs if x&T==T and x&forb==0}
                need(a==b,('tree fiber',n,G,T));ns+=1
            direct=[sum(hh[i]*(-1)**(j-i)*comb(r,j-i) for i in range(len(hh)) if 0<=j-i<=r) for j in range(m+1)]
            need(co==direct and co[0]==1 and co[-1]!=0,('degree/factorization',n,G))
            need(sum(map(abs,co))<=2**r*sum(hh)<=2**r*comb(m,r),('norm',n,G))
    need(ng==771,'coverage')
    return ng,ns

def values(N,a,b):
    # c[j]=b^{M_j} R_j(a/b), by size of the connected component of vertex 1;
    # the complement's internal edges sum to probability 1.
    C=[0,1]
    for n in range(2,N+1):
        C.append(b**M(n)-sum(comb(n-1,k-1)*C[k]*a**(k*(n-k))*b**M(n-k) for k in range(1,n)))
    return C

def endpoint():
    N=80;c=values(N,-1,1)
    # f'(-z)/f(-z)=g(z), g'=1+g^2, g(0)=1, in exponential coefficient convention.
    g=[1]
    for k in range(N-1):g.append((k==0)+sum(comb(k,h)*g[h]*g[k-h] for h in range(k+1)))
    for n in range(1,N+1):
        need(c[n]==(-1)**(M(n)+n-1)*g[n-1],('endpoint EGF',n))
    # Exact per-degree real brackets, not a demonstration of the limiting constant.
    brackets=[]
    for n in (7,8,15,16,31,32,63,64):
        lo=-1000;hi=0
        while hi-lo>1:
            mid=(lo+hi)//2
            C=values(n,mid,1000)[n]
            if C==0:lo=hi=mid;break
            if C<0:lo=mid
            else:hi=mid
        need(values(n,lo,1000)[n]<=0<=values(n,hi,1000)[n],('bracket',n))
        brackets.append((n,lo,hi))
    return brackets

if __name__=='__main__':
    n,t=exhaustive();bs=endpoint()
    print(f'PASS: {n} connected labelled simple graphs; {t} tree fibers; 80 exact endpoint evaluations.')
    print('Root brackets (n, 1000*left, 1000*right):',bs)
