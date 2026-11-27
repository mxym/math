#!/usr/bin/env python3
"""Independent binomial-symmetrized separator ranks and full-cube certificate checks."""
from fractions import Fraction as F
from math import comb


def dense_rank(M):
    M=[list(map(F,r)) for r in M]
    w=len(M[0]); d=0
    for j in range(w):
        pivot=next((i for i in range(d,len(M)) if M[i][j]),None)
        if pivot is None: continue
        M[d],M[pivot]=M[pivot],M[d]
        h=M[d][j]
        M[d]=[x/h for x in M[d]]
        for i in range(d+1,len(M)):
            h=M[i][j]
            if h: M[i]=[x-h*y for x,y in zip(M[i],M[d])]
        d+=1
        if d==len(M): break
    return d


def separator_rank(n,d):
    levels=[(0,t,1) for t in range(n+1)]+[(s,n+1-s,0) for s in range(1,n+1)]
    mon=[(i,j) for i in range(d+1) for j in range(d+1-i)]
    M=[[comb(s,i)*comb(t,j) for i,j in mon] for s,t,_ in levels]
    a=dense_rank(M)
    b=dense_rank([u+[w] for u,(_,_,w) in zip(M,levels)])
    return a,b


def mob_degree(y,n):
    entries=list(y)
    for i in range(n):
        mask=1<<i
        for j in range(1<<n):
            if j&mask: entries[j]-=entries[j^mask]
    return max((j.bit_count() for j,v in enumerate(entries) if v),default=-1)


def example(n):
    fives=[[],[],[],[],[]]
    threes=[[],[],[]]
    for z in range(1<<(2*n)):
        x = z & ((1<<n)-1)
        y = z >> n
        u=x.bit_count(); v=y.bit_count()
        a=x&1; b=x>>1&1
        U,V=u,u+v-n-1
        t=a+b
        g=(a,b,a-b,U,V)
        p=(0,0,0,int(u>0),int(u==0))
        w=(U*t,U*(t-1),V*(t-2))
        q=(int(t>=1),int(t==0 and u>0),int(u==0))
        assert sum(p)==sum(q)==1
        assert not all(g) and not all(w)
        assert any(g) and any(w)
        assert all(not v or g[i]!=0 for i,v in enumerate(p))
        assert all(not v or w[i]!=0 for i,v in enumerate(q))
        for i,v in enumerate(p): fives[i].append(v)
        for i,v in enumerate(q): threes[i].append(v)
    assert max(mob_degree(p,2*n) for p in fives)==n
    assert max(mob_degree(p,2*n) for p in threes)==n


def longer_redundancy():
    # The first three form a minimal cover on two coordinates, with
    # common zero 00. The single remaining form varies with all the
    # other 10 variables but stays nonzero there.
    n=12
    ans=[[],[],[],[]]
    for x in range(1<<n):
        a=x&1; b=x>>1&1
        row=(a,b,a-b,1+(x>>2).bit_count())
        i=next(i for i,v in enumerate(row) if v)
        assert 0 in row[:3]
        assert i==3 if a==b==0 else i<3
        for z in range(4): ans[z].append(int(z==i))
    assert max(mob_degree(p,n) for p in ans)==2


def main():
    rows=[]
    for n in range(2,9):
        a,b=separator_rank(n,n-1)
        c,d=separator_rank(n,n)
        assert b==a+1 and d==c
        example(n)
        rows.append((n,a,b,c,d))
    print('exact bivariate coefficient ranks (n, low rank, low augmented, high rank, high augmented):',rows)
    print('n=2..8: published five-affine and three-quadratic families both admit degree-n selectors')
    longer_redundancy()
    print('12-variable example: uncontrolled fourth form uses 10 variables, full certificate degree 2')
    print('PASS exact separator infeasibility/feasibility and independent full-cube certificates')


if __name__=='__main__': main()
