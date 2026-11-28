#!/usr/bin/env python3
"""Exact integer certificates for three strictly improving cyclotomic shortest-root bases."""
from itertools import product
from math import prod

# Each row: (r, lexicographic flat-index mask, threshold numerator, denominator).
DATA = (
    (7, 0xcbb0fcd90e22b270cc393904b2, 183, 200),
    (11, 0x1faa2f302f7680000fdf5fa5175f7b7043100201fd, 193, 200),
    (13, 0xffeed28a084141e9209e9fb15bffc761c604826f58ab2c87, 49, 50),
)


def det(A, positive=False):
    A=[r[:] for r in A]
    n=len(A)
    before=1
    sign=1
    for k in range(n-1):
        if positive:
            assert A[k][k]>0
        else:
            p=next((i for i in range(k,n) if A[i][k]),None)
            if p is None:
                return 0
            if p!=k:
                A[p],A[k]=A[k],A[p]
                sign=-sign
        p=A[k][k]
        for i in range(k+1,n):
            a=A[i][k]
            for j in range(k+1,n):
                v,r=divmod(p*A[i][j]-a*A[k][j],before)
                assert r==0
                A[i][j]=v
            A[i][k]=0
        before=p
    if positive:
        assert A[-1][-1]>0
    return sign*A[-1][-1]


def modrank2(cols):
    rows={}
    for vv in cols:
        x=sum((u%2)<<i for i,u in enumerate(vv))
        while x:
            k=x.bit_length()
            if k not in rows:
                rows[k]=x
                break
            x^=rows[k]
    return len(rows)


def verify(r,mask,a,b):
    shape=(3,5,r)
    domain=list(product(*(range(u) for u in shape)))
    reduced=list(product(*(range(u-1) for u in shape)))
    N,n=len(domain),len(reduced)
    assert n==8*(r-1) and N==15*r and a<b and mask.bit_length()<=N
    sel=[k for k in range(N) if (mask>>k)&1]
    comp=[k for k in range(N) if not ((mask>>k)&1)]
    assert len(sel)==n
    def table(s):
        v=domain[s]
        return tuple(prod(-1 if v[i]==shape[i]-1 else int(v[i]==u[i])
                         for i in range(3)) for u in reduced)
    M=[list(row) for row in zip(*(table(s) for s in sel))]
    detM=det(M)
    assert abs(detM)==1
    G=[[prod(shape[i]*int(domain[s][i]==domain[t][i])-1 for i in range(3))
           for t in sel] for s in sel]
    # Independently form the selected Gram through the powerful-basis columns.
    # Check a subset of independent integer contractions with the tensor Gram.
    mcols=list(zip(*M))
    kg=[[prod(shape[i]*int(u[i]==v[i])-1 for i in range(3))
          for v in reduced] for u in reduced]
    checks=0
    for i in range(0,n,4):
        v0=[sum(x*y for x,y in zip(mcols[i],row)) for row in kg]
        for j in range(0,n,5):
            assert G[i][j]==sum(x*y for x,y in zip(v0,mcols[j]))
            checks+=1
    defect=[[a*N*int(i==j)-b*x for j,x in enumerate(row)] for i,row in enumerate(G)]
    posdet=det(defect,positive=True)
    comp2=modrank2([table(s) for s in comp])
    return r,n,detM,posdet.bit_length(),comp2,checks



def inner(p,q,A,B):
    return sum((p*int(a[0]==b[0])-1)*(q*int(a[1]==b[1])-1)*x*y
               for a,x in A for b,y in B)


def letters(p,q):
    roots=list(product(range(p),range(q)))
    S=[((a,1),) for a in roots]
    M=[((a,1),(b,1)) for i,a in enumerate(roots) for b in roots[i+1:]
       if (a[0]==b[0] if p==3 else a[1]==b[1])]
    L=[((a,1),(b,-1)) for i,a in enumerate(roots) for b in roots[i+1:]
       if p==3 and a[0]!=b[0] and a[1]!=b[1]]
    return roots,S,M,L


def lpoly(x,u,y,v,a0,l):
    # (a0+t-1)^2 l^2 - (x+ut)(y+vt)
    d=a0-1
    return (l*l*d*d-x*y,2*l*l*d-u*y-v*x,l*l-u*v)


def table_and_polynomials():
    nrows=npoly=0
    for p,q,r0,LEN,bounds in (
      (3,5,17,(8,12,14),((0,1,6),(0,2,7),(1,2,4),(2,2,2))),
      (3,7,11,(12,20,22),((0,1,10),(0,2,11),(1,1,6),(1,2,8),(2,2,4))),
      (5,7,11,(24,36,0),((0,1,18),(1,1,6)))):
        _,*F=letters(p,q)
        for A,l in zip(F,LEN):
            assert all(inner(p,q,a,a)==l for a in A)
        for u,v,l in bounds:
            for i,a in enumerate(F[u]):
                for j,b in enumerate(F[v]):
                    if u==v and i>=j:
                        continue
                    if set(x for x,s in a).isdisjoint(y for y,s in b):
                        continue
                    assert abs(inner(p,q,a,b))>=l
                    nrows+=1
            s1,s2=p*q-LEN[u],p*q-LEN[v]
            d1,d2=s1*r0+LEN[u],s2*r0+LEN[v]
            x,y,z=lpoly(d1,s1,d2,s2,r0,l)
            assert x>0 and y>=0 and z>=0
            npoly+=1
    return nrows,npoly


def mixed_restrictions():
    count1=count2=0
    for p,q,rs in ((3,5,(17,19,23,29,31)),(3,7,(11,13))):
        roots,*F=letters(p,q)
        D=( (0,1),(0,2),(1,2),(2,3) )
        for r in rs:
            X=[]
            for a,b in product(roots,repeat=2):
                va,vb=((a,1),),((b,1),)
                f=inner(p,q,va,vb)
                if f<0:
                    vb=((b,-1),)
                df=p*q*r-r*(inner(p,q,va,va)+inner(p,q,vb,vb))
                df+=inner(p,q,va+vb,va+vb)
                if df>=0:
                    X.append((va,vb,df))
            assert max(v[2] for v in X)<=15
            for a,b,dx in X:
                for B in F:
                    for w in B:
                        dp=p*q*r-(r-1)*inner(p,q,w,w)
                        if dp<0:
                            continue
                        for u in (a,b):
                            if u[0][0] not in tuple(v for v,s in w):
                                continue
                            ip=r*inner(p,q,u,w)-inner(p,q,a+b,w)
                            assert ip**2>dx*dp
                            count1+=1
                for c,d,dy in X:
                    for I in D:
                        L=[]
                        for i,w in zip((0,1),(a,b)):
                            for j,v in zip(I,(c,d)):
                                if i==j:
                                    L.append((w,v))
                        if not any(w[0][0]==v[0][0] for w,v in L):
                            continue
                        if a==c and b==d and I==(0,1):
                            continue
                        ip=r*sum(inner(p,q,w,v) for w,v in L)-inner(p,q,a+b,c+d)
                        assert ip**2>dx*dy
                        count2+=1
    return count1,count2


if __name__=="__main__":
    for row in DATA:
        print("PASS: r/rank/det/defect bits/complement rank F2/Gram", *verify(*row))
    print("PASS: pure overlaps/squared-polynomial rows", *table_and_polynomials())
    print("PASS: mixed-pure and mixed-mixed overlaps", *mixed_restrictions())
