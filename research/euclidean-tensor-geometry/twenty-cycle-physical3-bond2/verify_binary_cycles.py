from itertools import product
from collections import defaultdict
import sys
from pathlib import Path
import numpy as np
s=10; p=251; t=7
W=3**s; H=W//3
w=[tuple((u//3**i)%3 for i in range(s)) for u in range(W)]
charge=[a.count(1)-a.count(2) for a in w]
rot=lambda u:u//3+H*(u%3)
tri=(0,1,-1)
refl=lambda u:sum((3-w[u][(-i)%s] if w[u][(-i)%s] else 0)*3**i for i in range(s))
Rp=[None]*W; O={}
for u in range(W):
    if Rp[u] is not None: continue
    o=[];v=u
    while not o or v!=u:
        Rp[v]=(u,len(o));o.append(v);v=rot(v)
    O[u]=o
# Enumerate closed binary walks, rather than trace-testing each pair of words.
D=defaultdict(int); E=defaultdict(int); Z=[pow(t,i,p) for i in range(2*s+1)]
for v in range(1<<(2*s)):
    b=[(v>>i)&1 for i in range(2*s)]; b.append(b[0]);a=c=e=h=0; power=1
    for i in range(s):
        d=b[2*i+1]-b[2*i]; f=b[2*i+2]-b[2*i+1];h+=d
        a+=(d%3)*power;c+=(f%3)*power;power*=3
        e+=(b[2*i] if d==0 else 0)+(b[2*i+1] if f==0 else 0)
    if h<0 or Rp[a][0]!=a: continue
    cu,ci=Rp[c];D[a,cu,ci]=(D[a,cu,ci]+Z[e])%p
    if h==0: E[a,cu,ci,e]+=1

def rank(a, p):
    k=0
    for j in range(a.shape[1]):
        nz=np.flatnonzero(a[k:,j])
        if not nz.size: continue
        i=k+int(nz[0]);a[[k,i]]=a[[i,k]]
        r=k+1+np.flatnonzero(a[k+1:,j]); d=(a[r,j]*pow(int(a[k,j]),-1,p))%p
        if r.size:a[r,j:]=(a[r,j:]-d[:,None]*a[k,j:])%p
        k+=1
    return k

def pencil_check(relfile):
    B={1:[],-1:[]}
    for u,o in O.items():
        if charge[u] or len(o)%2: continue
        v,shift=Rp[refl(u)]; phase=(-1)**shift
        if v<u: continue
        if v==u: B[phase].append([(u,1)])
        else:
            for sg in B:B[sg].append([(u,1),(v,sg*phase)])
    rb,cb=sorted(B.values(),key=len); assert (len(rb),len(cb))==(405,486)
    r_idx={a[0][0]:i for i,a in enumerate(rb)}
    c_idx={c:(j,sign) for j,lst in enumerate(cb) for c,sign in lst}
    rho=lambda u:(-2*sum(i*tri[d] for i,d in enumerate(w[u]))-w[u].count(1))%(2*s)
    mats=[defaultdict(int) for _ in rb]
    for (a,c,k,d),x in E.items():
        if a not in r_idx or c not in c_idx: continue
        j,sign=c_idx[c]; h=rho(a)+rho(c)
        assert d==h%(2*s)
        mats[r_idx[a]][j,h//(2*s)] += sign*(-1)**k*x
    ls=[[[int(f) for f in z.split(':')] for z in line.split()] for line in Path(relfile).read_text().splitlines() if line.strip()]
    val=pow(7,-2*s,101); v=np.zeros((len(ls),len(rb)),dtype=np.int32)
    for k,L in enumerate(ls):
        acc=defaultdict(int)
        for i,e,c in L:
            assert 0<=i<len(rb) and 0<=e<=1
            v[k,i]=(v[k,i]+c*pow(val,e,101))%101
            for (j,d),x in mats[i].items():acc[j,d+e]+=c*x
        assert all(c==0 for c in acc.values())
    assert len(ls)==rank(v,101)==86
    print('pencil dimensions 405 486; 86 independent polynomial null rows, all coefficients zero',flush=True)

if len(sys.argv)>1:pencil_check(sys.argv[1])
z=next(a for a in range(2,p) if pow(a,s,p)==1 and all(pow(a,k,p)!=1 for k in range(1,s)))
R=0; defects=[]; size=0
for q in range(s+1):
    for k in range(s):
        rs={r:i for i,r in enumerate(u for u in O if charge[u]==q and k*len(O[u])%s==0)}
        cs={c:j for j,c in enumerate(u for u in O if charge[u]==-q and k*len(O[u])%s==0)}
        assert len(rs)==len(cs)
        M=np.zeros((len(rs),len(cs)),dtype=np.int32); zps=[pow(z,k*j,p) for j in range(s)]
        for (a,c,j),v in D.items():
            if a in rs and c in cs:
                r=rs[a]; l=cs[c]; M[r,l]=(M[r,l]+v*zps[j])%p
        n=len(rs); r=rank(M,p)
        if r<n:defects.append((q,k,n,n-r))
        R+=(1 if q==0 else 2)*r; size+=(1 if q==0 else 2)*n
    print('charge',q,'complete',flush=True)
print('dimensions',size,'rank',R,'defects',defects,flush=True)
assert (size,R,defects)==(59049,58796,[(0,5,891,253)])
