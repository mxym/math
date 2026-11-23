"""Two original Fano directions at rank 36: exact F7 graph-mark check.
Dependency: the companion two_fano_core.py, plus NumPy (integer arrays only).
"""
from two_fano_core import labeled, blocks, sides
from itertools import combinations, product
from collections import Counter
import numpy as np
N=labeled(15)
sq=(1,2,4)
def cap(i,j):return int(2-int(j in N[i])-len(N[i]&N[j]))
def options(j):
    X,Y=map(sorted,blocks[j:j+2])
    return [(x,y) for x in X for y in Y if cap(x,y)>0]
def tables():
    X,Y=map(sorted,blocks[2:4])
    rows=[]
    for x in X:
        rows.append([v for v in product(*(range(1+cap(x,y)) for y in Y)) if sum(v)==3])
    def rec(i,T,b):
        if i==5:
            assert b==(0,)*5
            yield T
            return
        for r in rows[i]:
            if any(a>u for a,u in zip(r,b)):continue
            yield from rec(i+1,T+[r],tuple(u-a for a,u in zip(r,b)))
    yield from rec(0,[],(3,)*5)
def piv(M):
    a=M.copy()%7;i=0;I=[]
    for j in range(a.shape[1]):
        ks=np.flatnonzero(a[i:,j])
        if not len(ks):continue
        k=i+ks[0];a[[k,i]]=a[[i,k]]
        a[i]=a[i]*pow(int(a[i,j]),-1,7)%7
        a[i+1:]=(a[i+1:]-a[i+1:,j,None]*a[i])%7
        I.append(j);i+=1
        if i==len(a):break
    return I
def inv(M):
    n=len(M);a=np.hstack((M.copy()%7,np.eye(n,dtype=int)));d=1
    for j in range(n):
        k=j+np.flatnonzero(a[j:,j])[0]
        if k!=j:a[[j,k]]=a[[k,j]];d=-d
        t=int(a[j,j]);d=d*t%7;a[j]=a[j]*pow(t,-1,7)%7
        coeff=a[:,j].copy();coeff[j]=0
        a=(a-coeff[:,None]*a[j])%7
    return d%7,a[:,n:]
def core():
    H=np.array([[3*int(x==y)-int(y in N[x])+4 for y in range(24)] for x in range(24)])
    U=np.array([[int(x in sides[j])-int(x in sides[j+1]) for x in range(24)] for j in [0,2]])
    return np.block([[H,U.T],[U,2*np.eye(2,dtype=int)]])
def first(T,d=2):
    X,Y=map(sorted,blocks[2:4])
    pairs=[(x,y) for i,x in enumerate(X) for j,y in enumerate(Y) for _ in range(T[i][j])]
    w=np.zeros((15,24+d),dtype=int);w[:,:24]=4
    for i,(x,y) in enumerate(pairs):w[i,[x,y]]-=1
    return w
def maxcl(A):
    a=[sum(1<<j for j in range(len(A)) if i!=j and A[i,j]) for i in range(len(A))]
    best=0
    def run(mask,n):
        nonlocal best
        if n>best:best=n
        while mask and n+mask.bit_count()>best:
            v=mask&(-mask);mask^=v
            run(mask&a[v.bit_length()-1],n+1)
    run((1<<len(A))-1,0)
    return best
def second(A):
    I=piv(A);d,R=inv(A[np.ix_(I,I)])
    assert len(I)==36 and d not in sq
    wr=[]
    for x,y in options(0):
        for tr in combinations(range(15),3):
            w=np.full(41,4);w[[24,25]]=0;w[[x,y]]-=1;w[[26+i for i in tr]]-=1
            wr.append(w)
    wr=np.array(wr);v=wr[:,I]@R%7
    use=np.all((v@A[I,:]-wr)%7==0,axis=1)&(np.sum(wr[:,I]*v,axis=1)%7==0)
    w=wr[use];v=v[use]
    return len(w),maxcl((v@w[:,I].T)%7==4)
def main():
    H=core();I=piv(H);d,R=inv(H[np.ix_(I,I)])
    assert len(I)==24 and d not in sq and len(options(0))==23
    S=3*np.eye(15,dtype=int)+4
    hist=Counter();last=Counter()
    for T in tables():
        U=first(T);K=(S-U[:,I]@R@U[:,I].T)%7
        J=piv(K);e,_=inv(K[np.ix_(J,J)])
        hist[len(J),e in sq]+=1
        if len(J)>12 or (len(J)==12 and e not in sq):continue
        last[second(np.block([[H,U.T],[U,S]]))]+=1
    print('projected rank and square determinant:',sorted(hist.items()))
    print('(candidate sites, maximum clique):',sorted(last.items()))
    assert hist=={(14,False):2153,(14,True):1716,(13,False):923,(13,True):173,(12,True):22}
    assert last=={(36,4):6,(37,4):4,(37,3):4,(27,3):4,(35,3):2,(39,3):2}
if __name__=='__main__':main()
