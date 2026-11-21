"""Exact finite-field controls. Python standard library, python3 -O works."""
from fractions import Fraction
from itertools import product
from math import gcd

def check(ok, msg):
    if not ok: raise ValueError(msg)

def factor(n):
    d=2; a={}
    while d*d<=n:
        while n%d==0:
            a[d]=a.get(d,0)+1; n//=d
        d=3 if d==2 else d+2
    if n>1:a[n]=a.get(n,0)+1
    return a

def signature(N,root):
    labels=[root]; fac={}
    for x in labels:
        check(gcd(x,N)==1 and factor(x)=={x:1},'not a unit prime')
        f=fac[x]=factor(N-x)
        check(sum(f.values())>=2,'prime complement')
        for q in f:
            if q not in labels:labels.append(q)
    for x in labels:
        reached={x};todo=[x]
        for y in todo:
            for z in fac[y]:
                if z not in reached: reached.add(z);todo.append(z)
        check(len(reached)==len(labels),'not strongly connected')
    A=[[fac[x].get(y,0) for y in labels] for x in labels]
    return A,[[int(i==j)-v for j,v in enumerate(row)] for i,row in enumerate(A)]

def affine(M,b,p):
    # Standard row reduction, with rational arithmetic if p=0.
    red=(lambda t: t%p) if p else Fraction
    inv=(lambda t: pow(t,-1,p)) if p else (lambda t:1/t)
    a=[[red(x) for x in row]+[red(rhs)] for row,rhs in zip(M,b)]
    n=len(M[0]);key=[];r=0
    for c in range(n):
        pivot=next((j for j in range(r,len(a)) if a[j][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        u=inv(a[r][c]);a[r]=[red(t*u) for t in a[r]]
        for j,row in enumerate(a):
            if j!=r and row[c]:
                u=row[c];a[j]=[red(s-u*t) for s,t in zip(row,a[r])]
        key.append(c);r+=1
    if any(row[-1] for row in a[r:]):return None,None
    x=[0]*n
    for j,c in enumerate(key):x[c]=a[j][-1]
    basis=[]
    for free in [i for i in range(n) if i not in key]:
        v=[0]*n;v[free]=1
        for j,c in enumerate(key):v[c]=red(-a[j][free])
        basis.append(v)
    return x,basis

def allsol(M,h,p):
    x,V=affine(M,[h]*len(M),p)
    if x is None:return []
    return [tuple((x[i]+sum(a*v[i] for a,v in zip(cs,V)))%p
            for i in range(len(x))) for cs in product(range(p),repeat=len(V))]

def ranks(B,l):
    n=len(B);V=affine(B,[0]*n,l)[1];C=affine(list(zip(*B)),[0]*n,l)[1]
    r=len(affine(B,[0]*n,0)[1])
    check(len(C)==len(V)==r,'kernel reduction changes rank in control')
    return r,C,V

def control(N,root,l,gen,expected):
    A,B=signature(N,root);n=len(B);r,C,V=ranks(B,l)
    m=l-1;zs=allsol(B,(m//2)%2,2)
    if l==11:
        z5=allsol(B,(m//2)%5,5)
        zs=[tuple((5*a+6*b)%10 for a,b in zip(x,y)) for x,y in product(zs,z5)]
    else:check(l==3,'supported test bases')
    check(len({pow(gen,j,l) for j in range(m)})==m,'bad primitive root')
    compatible=bad=0
    for z in zs:
        x=[pow(gen,t,l) for t in z]; inv=[pow(t,-1,l) for t in x]
        for i,row in enumerate(A):
            pr=1
            for a,y in zip(row,x):pr=pr*pow(y,a,l)%l
            check((pr+x[i])%l==0,'monomial mask')
        if any(sum(a*y for a,y in zip(c,inv))%l for c in C):continue
        compatible+=1
        j=[[sum(a*b*h for a,b,h in zip(c,v,inv))%l for v in V] for c in C]
        if affine(j,[0]*r,l)[1]:bad+=1
    result=(n,r,len(zs),compatible,bad)
    check(result==expected,'control mismatch')
    print(N,l,'(k,r,monomial,compatible,nontransverse)',result)

def positive128():
    A,B=signature(128,3);n=len(B);r,C,V=ranks(B,2)
    check(n==8 and r==1 and sum(a*b for a,b in zip(C[0],V[0]))%2==1,'128 transversality')
    colors=[0]*n;counts=[1]
    while True:
        prof=[(colors[i],tuple(sum(row[j] for j in range(n) if colors[j]==c)
              for c in range(1+max(colors)))) for i,row in enumerate(A)]
        uniq=sorted(set(prof))
        if len(uniq)==counts[-1]:break
        colors=[uniq.index(z) for z in prof];counts.append(len(uniq))
    check(counts==[1,2,6,8],'128 color refinement')
    print('128 true positive, odd kernel pairing, color counts',counts)

if __name__=='__main__':
    positive128()
    control(1862,3,11,2,(21,2,200,3,0))
    control(6142,17,3,2,(10,3,16,2,0))
