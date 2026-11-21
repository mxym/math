"""Independent descending exhaustive certificate for projected rows, then exact terminal tests.
PYTHONOPTIMIZE is safe. Usage: python3 -O charts_reverse.py weights.txt [terminals.txt].
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement,product
from math import gcd,lcm,prod
import sys
P=101
def fail(s):raise RuntimeError(s)
def rref(matrix,n):
    a=[list(map(F,r)) for r in matrix]; piv=[]
    for j in range(n):
        h=len(piv); i=next((i for i in range(h,len(a)) if a[i][j]),None)
        if i is None:continue
        a[i],a[h]=a[h],a[i]
        f=a[h][j];a[h]=[x/f for x in a[h]]
        for i in range(len(a)):
            if i!=h and a[i][j]:a[i]=[x-a[i][j]*y for x,y in zip(a[i],a[h])]
        piv.append(j)
    return a,piv
def null(matrix,n):
    a,p=rref(matrix,n);ns=[]
    for j in range(n):
        if j not in p:
            v=[F(0)]*n;v[j]=1
            for i,k in enumerate(p):v[k]=-a[i][j]
            ns.append(v)
    return ns
def rank(a,n):return len(rref(a,n)[1])
def det(a):
    a=[list(map(F,r)) for r in a];v=F(1)
    for i in range(len(a)):
        k=next((l for l in range(i,len(a)) if a[l][i]),None)
        if k is None:return F(0)
        if k!=i:a[k],a[i]=a[i],a[k];v=-v
        v*=a[i][i]
        for k in range(i+1,len(a)):
            z=a[k][i]/a[i][i]
            for j in range(i+1,len(a)):a[k][j]-=z*a[i][j]
    return v
def insert(basis,vec):
    v=list(vec)
    for j,b in basis:
        t=v[j]
        if t:
            for k in range(j,5):v[k]=(v[k]-t*b[k])%P
    j=next((j for j,x in enumerate(v) if x),None)
    if j is None:return basis
    if len(basis)==4:return None
    inv=pow(v[j],-1,P);v=tuple(x*inv%P for x in v)
    return tuple(sorted((*basis,(j,v))))
def exact(idx,w,d,A):
    g=0
    for x in A[0]:g=gcd(g,x)
    if g!=1:return
    reached={0}
    for _ in range(6):reached|={j+1 for i in reached for j in range(5) if A[i][j]}
    if len(reached)!=6:return
    B=[[int(i==j+1)-A[i][j] for j in range(5)] for i in range(6)]
    ns=null(B,5)
    if len(ns)!=1 or not ns[0][0] or rank(A,5)!=5:return
    k=lcm(*(F(z).denominator for z in ns[0]))
    v=[0]+[int(k*z) for z in ns[0]] # integral multiple; p coordinate is zero
    if min(sum(z<0 for z in v),sum(z>0 for z in v))<2:return
    m=d//2+1; small=[v[i] for i,n in enumerate((0,)+w) if n<m]
    if len(set(small))!=len(small):return
    if not any(all(s[i]==-prod(s[j+1]**a for j,a in enumerate(r)) for i,r in enumerate(A)) for s in ((1,)+x for x in product((-1,1),repeat=5))):return
    return B,v
def terminal(d,w,A,B,v): # all products/identities are checked over Q
    if w[0]!=1:fail("unhandled degree of least label")
    if d==5:
        L=null(list(zip(*B)),6)
        T=[[(F(x)*v[j]**t) for j,x in enumerate(c)] for t in range(3) for c in L]
        h=det(T)
        if not h:fail("quintic survived")
        return 'moment6-det='+str(h)+'; vector='+','.join(map(str,v))
    if d!=3 or any(n not in (1,2) for n in w) or w.count(2)>1:fail("unhandled profile")
    z=next((j for j,n in enumerate(w) if n==2),None)
    eq=[];full=[]
    for i,r in enumerate(A):
        if ((0,)+w)[i]>=2:continue
        fixed=sum((F(a,v[j+1]) for j,a in enumerate(r) if a and w[j]==1),F(0))
        eq.append([r[z] if z is not None else 0,-1]);full.append(eq[-1]+[-fixed])
    if rank(eq,2)==rank(full,3):fail("cubic survived")
    return 'incompatible b,C equations (b coeff, C coeff, rhs)='+str(full).replace('Fraction','F')+'; vector='+','.join(map(str,v))
def run(ws,termfile):
    terms=[];raw=[]
    for idx,row in enumerate(ws,1):
        w=tuple(row[:5]);d=row[5];R=set()
        for n in range(2,8):
            for t in combinations_with_replacement(range(5),n):
                if sum(w[j] for j in t)==d:R.add(tuple(t.count(j) for j in range(5)))
        R=sorted(R); opts=[]
        for i in range(6):
            g=[]
            for j,r in enumerate(R):
                if i and r[i-1]:continue
                up=sum(1<<k for k in range(i,5) if r[k])
                b=tuple((int(i==k+1)-r[k])%P for k in range(5))
                g.append((j,1<<j,up,b))
            opts.append(g)
        ids=[-1]*6
        def descend(i,used,up,bs):
            if i<0:
                A=[R[j] for j in ids]
                res=exact(idx,w,d,A)
                if res:
                    B,v=res; tag='raw '+str(idx)+' '+' '.join(map(str,ids))
                    raw.append((idx,tuple(ids)));terms.append((idx,tuple(ids),tag+'  '+terminal(d,w,A,B,v)))
                return
            for j,bit,high,b in opts[i]:
                if used&bit or up&high:continue
                nb=insert(bs,b)
                if nb is None:continue
                ids[i]=j;descend(i-1,used|bit,up|high,nb)
        descend(5,0,0,())
    for idx,ids in sorted(raw):print('raw',idx,*ids)
    if termfile:
        with open(termfile,'w') as h:
            for _,__,s in sorted(terms):h.write(s+'\n')
    if len(raw)!=32:fail("unexpected census size")
if __name__=='__main__':
    with open(sys.argv[1]) as f: ws=[tuple(map(int,l.split())) for l in f if l.strip()]
    run(ws,sys.argv[2] if len(sys.argv)>2 else None)
