#!/usr/bin/env python3
"""Replay an exact finite covering. Pure stdlib; no LP, search, floats or asserts."""
import sys,json,math
from fractions import Fraction as Q
from itertools import combinations
from functools import lru_cache
from bisect import bisect_left
from pathlib import Path
from collections import Counter
def ck(x,msg):
    if not x:raise ValueError(msg)
def integer(x):return type(x) is int
def affine(h,v):return h[0]+h[1]*v[0]+h[2]*v[1]
def differences(a,b):return tuple(x-y for x,y in zip(a,b))
def rows(k):
    b=k-1
    for r in range(b+1):
        for j in range(13):
            t=Q(r,b);p=Q(j,12);h=Q(2*r*(b-r),b*(b-1)) if b>1 else Q(0)
            g=2*p*(1-p);x=p+t-2*p*t
            yield (h-x,t-p,g-x),(-x,1,x-p)
    yield (-1,0,0),(0,0,0)
    yield (0,-1,0),(0,0,0)
    yield (0,0,-1),(0,0,0)
    yield (0,1,0),(0,0,1)
    yield (1,0,1),(1,0,-1)
    if b==1:yield (1,0,0),(0,0,0)
def determinant(a):
    if len(a)==0:return Q(1)
    return sum((-1)**i*x*determinant([r[:i]+r[i+1:] for r in a[1:]]) for i,x in enumerate(a[0]))
def make_plane(k,w,base):
    if w=='mass':return (2,0,0)
    if w=='max':return (0,0,k)
    ck(type(w) is list and 1<=len(w)<=3 and all(integer(i) and 0<=i<len(base) for i in w) and len(set(w))==len(w),'bad row indexes')
    goal=[1,1,-1];n=len(w); sel=[base[i] for i in w]
    for I in combinations(range(3),n):
        m=[[Q(p[0][i]) for p in sel] for i in I];d=determinant(m)
        if not d:continue
        l=[determinant([r[:j]+[goal[i]]+r[j+1:] for r,i in zip(m,I)])/d for j in range(n)]
        ck(min(l)>=0 and all(sum(lam*p[0][i] for lam,p in zip(l,sel))==goal[i] for i in range(3)),'invalid combination')
        return tuple(int(i==0)+sum(lam*p[1][i] for lam,p in zip(l,sel)) for i in range(3))
    raise ValueError('dependent support')
def clip(vertices,h):
    v=[];a=vertices[-1];A=affine(h,a)
    for b in vertices:
        B=affine(h,b)
        if A*B<0:v.append(tuple((A*y-B*x)/(A-B) for x,y in zip(a,b)))
        if B>=0:v.append(b)
        a,A=b,B
    return v
def twice_area(v):return sum(a[0]*b[1]-a[1]*b[0] for a,b in zip(v,v[1:]+v[:1]))
def sums(blocks):
    c={0:1}
    for x,n in blocks:
        u=Counter()
        for j in range(n+1):
            m=math.comb(n,j)
            for s,f in c.items():u[s+(n-2*j)*x]+=m*f
        c=u
    return c
def khintchine(l):
    den=math.lcm(*(a.denominator for a in l))
    counts=Counter(int(a*den) for a in l if a);a=[];b=[];u=v=1
    for x,n in sorted(counts.items(),key=lambda t:-t[1]):
        if u<=v:a.append((x,n));u*=n+1
        else:b.append((x,n));v*=n+1
    h=sums(a);j=sums(b);keys=sorted(j);cs=[0];sv=[0]
    for x in keys:cs.append(cs[-1]+j[x]);sv.append(sv[-1]+x*j[x])
    val=0
    for x,m in h.items():
        i=bisect_left(keys,-x)
        val+=m*((cs[-1]-2*cs[i])*x+sv[-1]-2*sv[i])
    cnt=2**sum(counts.values());ck(sum(h.values())*cs[-1]==cnt,'count')
    return Q(val,den*cnt)
def upper(y):
    # From each index choose farthest maximizer of forward secant. Verify the
    # resulting slopes' order, signs, total, and every original prefix directly.
    i=0;a=[]
    while i<len(y)-1:
        x,j=max(((y[j]-y[i])/(j-i),j) for j in range(i+1,len(y)))
        a += [x]*(j-i); i=j
    ck(len(a)==32 and min(a)>=0 and sum(a)==2 and all(s>=t for s,t in zip(a,a[1:])),'bad majorant')
    ck(all(sum(a[:k])>=z for k,z in enumerate(y)),'missing prefix')
    return a
def run(file):
    d=json.loads(Path(file).read_text());ck(set(d)=={'bounds','cells','version'} and d['version']==1,'schema')
    ds=d['bounds'];ck(len(ds)==30,'number bounds');catalog={}
    for k,ds1 in enumerate(ds,2):
        base=list(rows(k));catalog[k]=[make_plane(k,w,base) for w in ds1]
    def P(k,s):
        ck(integer(k) and 2<=k<=31 and integer(s) and 0<=s<len(catalog[k]),'plane index');return catalog[k][s]
    lo=Q(1,2);hi=Q(2,3);v=[(lo,Q(0)),(hi,Q(0)),(hi,hi),(lo,hi)]
    for j in range(13):
        p=Q(j,12);g=2*p*(1-p);v=clip(v,(-g,1,g-p))
    ck(twice_area(v)>0,'empty root')
    t=Counter();area=0; strict=[]
    @lru_cache(maxsize=15000)
    def checkcorner(z,H):
        y=[Q(0),z[1]]+[Q(affine(P(k,i),z)) for k,i in enumerate(H,2)]+[Q(2)]
        a=upper(y);budget=(15*z[0]-6)/4;ck(budget>0,'budget')
        sq=sum(x*x for x in a)
        if sq<budget**2:
            strict.append((budget**2-sq)/(2*budget));t['strict square']+=1
            return 0
        v=khintchine(a)
        ck(v<=budget,('violated',z));t['exact L1']+=1
        if v<budget:
            strict.append(budget-v);return 0
        b=tuple(x for x in a if x)
        ck(len(b) in (3,5),'support')
        ck((len(b),z[0]) in ((3,Q(2,3)),(5,Q(3,5))),'cut level')
        from itertools import product
        for signs in product((-1,1),repeat=len(b)):
            ma=1 if sum(signs)>0 else -1
            ck(ma*sum(x*y for x,y in zip(b,signs))>=Q(23,65),'majority gap')
        return len(b)
    def checktree(u,z):
        nonlocal area
        ck(type(u) is list and len(u) in (1,3),'bad node')
        if len(u)==1:
            H=u[0];ck(type(H) is list and len(H)==30,'bad choices')
            kinds={checkcorner(q,tuple(H)) for q in z}-{0}
            ck(len(kinds)<=1,'mixed tight leaf')
            t['leaves']+=1;t['corner incidences']+=len(z);area+=twice_area(z);return
        k,i,j=u[0];f=differences(P(k,i),P(k,j));left=clip(z,f);right=clip(z,tuple(-h for h in f))
        l=twice_area(left);r=twice_area(right)
        ck(l>0 and r>0 and l+r==twice_area(z),'cut is not a genuine partition')
        t['splits']+=1;checktree(u[1],left);checktree(u[2],right)
    checktree(d['cells'],v)
    ck(t['splits']==t['leaves']-1 and area==twice_area(v),'failed final area')
    print('K=32; p=j/12; validated prefix bounds:',sum(map(len,catalog.values())))
    ck(strict and min(strict)>0,'strict gaps')
    print('certified rational eta:',min(strict))
    print('no mixed tight leaves and majority margins >= 23/65')
    print(dict(t));print('Twice checked total root area:',area);print('PASS')
if __name__=='__main__':run(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('certificate.json'))
