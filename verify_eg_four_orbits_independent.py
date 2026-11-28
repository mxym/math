#!/usr/bin/env python3
"""Independent four-layer audit. SymPy HNF indexes cells; determinantal divisors test membership."""
from itertools import combinations,permutations,product
from math import gcd
from functools import lru_cache
from json import loads
from base64 import b85decode
from zlib import decompress
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
data=loads(decompress(b85decode("c$}43S(5574E*O5)O?#NTY-?gt5BR|YVQ8L$c`noO<;;yGOexEk`sO}*Xxf@uRs+1&%f($yb`ay-tqUBcTcyu;K)7l+q>PZ@$b7^();Zg{0i<CoPR5$5Hh-225-%LG<>^glRO;u5&AIR6D$G+N;#{(LZ3=`YnMH^c&2gu8lGyA%!tHrDb$s+D^~=GQodr8VH|SC9&}?6gBy|zYC~|9eE}=KXPkV|8pRDv;Df6hXmidkg8p2UbjU9&=`~lsX43Xd&6B@xS|N?ZHTmB&b>(|xGUFo%Sm{c)gkKPf1nR+QjL?9e6$twPvxZ=4ryY@UG~!D2q&T!-lEf~J)BR|Jr4>w|Nunz8K1f*q)Hxy6X4ucf$Z`L=*hML@K&?9JJP<c^88wxLJbvb=-|^<3-l;lkwRupEA+s85!|dg>WRBLpQmFqK9ezv$1l5>m(|yy1n;xouFQuhKzTZo^pziotJ8|gp8vz}@oN$@!vgUbT^941gN8#2NuX=3(Visf<lMmTJ%r;x?ur)CiM?~IFILh>gT&p}Ea)l`4(A|QBb{w)Fowdvr_}i-Sss3cFXiz&&P~0YR%hnOM=ZmtY!0p>iN<cnd%O{+f*53TXAa-Em+5>HQtu0_>XRbH@cu4KXq7s7|DfLK%gvTNHy5RzEKXFA1)HK#w$XwFv%UnuL&RqE>7r+aRc{#-fsoH2<+o_63=NA*4`^!Vb3UAw-x+}duvh{*8sg_xfyRe|9V@r*@LEs{JBg-40iz;2AURjU;u;q!o*rCXa68$i*HpZUQ+6S@}IrUZ&bVDeq*C+={=_oyjo6w~wAd#H!09X-VgNU1A=|DZmgdwiD1<Ue`#Zg$UOBL40D39G+-nFSwPd+R6K24G{*4c;~SO8Lvf_2n(_r_mn=O6d$LRs0WjMMQK+UARTfPY9QyUo+{Ei$}Sp43*dJd>n3plZPT7fI?*CeA0hoM@KqXm|8;KCoM1#KYF4*1Xwn5vzO1ypmo|-jE1mL-iH~iOS>|K*Q>XIOk(dAHW7S@DXn`f<b~n(`>`2(MGyq2i*CQNIVNR@RWTPE;;xKm<Z|TAvKL>Le7}Mi>H4GMvF&L1KNF`=egMy9uaXsKMxq@y{G}x>2UeG{0I8sWQq")))
E=list(combinations(range(4),2)); V=tuple(range(4))
def shapes():
    total=0; orbit=set()
    for mask in range(64):
        used=[e for j,e in enumerate(E) if mask>>j&1];parts=[{v} for v in V]
        for a,b in used:
            U=next(u for u in parts if a in u);W=next(u for u in parts if b in u)
            if U!=W:parts.remove(W);U.update(W)
        if len(parts)>1:continue
        for k in range(3):
            for extra in combinations(used,k):
                if len(set(sum((list(e) for e in extra),[])))!=2*k:continue
                mult={e:(e in used)+(e in extra) for e in E}
                deg=[sum(m for e,m in mult.items() if i in e) for i in V]
                for loops in product(*[(0,) if d>=3 else tuple(range(3-d,3)) for d in deg]):
                    g=[x+y for x,y in zip(deg,loops)]
                    if any((loops[i]*loops[j] or min(g[i],g[j])>3) for i,j in used):continue
                    total+=1
                    orbit.add(min(''.join(map(str,[loops[i] for i in r]+[mult[tuple(sorted((r[i],r[j])))] for i,j in E])) for r in permutations(V)))
    assert total==179 and orbit==data.keys()
def arrowdata(name):
    n=0;arr=[];avoid=[];relations=[];tree=[];used=[]
    def gen():
        nonlocal n
        n+=1;return (n,1)
    def arc(i,j,z,invol=False):
        t=len(arr);arr.append((i,j,z,t if invol else t+1))
        if not invol:arr.append((j,i,(z[0],-z[1]),t))
    # Greedy tree decided by enumerating earlier paths, not by the author's component union.
    for (i,j),cnt in zip(E,map(int,name[4:])):
        if not cnt:continue
        reach={i}
        for _ in V:
            reach|={a for e in tree if set(e)&reach for a in e}
        v=gen() if j in reach else (0,0)
        if v==(0,0):tree.append((i,j))
        arc(i,j,v)
        if cnt==2:
            w=gen();arc(i,j,w);avoid.append([w,(v[0],-v[1])])
    for i,x in enumerate(map(int,name[:4])):
        if x:
            g=gen();arc(i,i,g,x==1);avoid.append([(g[0],x)])
            if x==1:relations.append([(g[0],2)])
    def expand(z):
        a=[0]*n
        for i,b in z:
            if i:a[i-1]+=b
        return tuple(a)
    return n,[(i,j,expand([z]),k)for i,j,z,k in arr],tuple(map(expand,avoid)),tuple(map(expand,relations))
@lru_cache(None)
def key(R,n):
    if not R:return ()
    M=hermite_normal_form(Matrix(R).T).T
    return tuple(tuple(int(x)for x in row)for row in M.tolist())
@lru_cache(None)
def rank_index(R,n):
    # gcd of all maximal minors is the index in the common rational saturation.
    if not R:return (0,1)
    A=Matrix(R);r=A.rank();z=0
    for I in combinations(range(len(R)),r):
        for J in combinations(range(n),r):z=gcd(z,int(A.extract(I,J).det()))
    return (r,z)
def has(R,v,n):
    return rank_index(R+(v,),n)==rank_index(R,n)
def walk(ar,w,n):
    assert len(w) in (4,8,16) and all(0<=j<len(ar)for j in w)
    z=(0,)*n;slots=[[] for j in V];D=set()
    for i,j in enumerate(w):
        a,b,v,rev=ar[j];nextj=w[(i+1)%len(w)]
        assert ar[nextj][0]==b and nextj!=rev
        for y in slots[a]:D.add(tuple(t-u for t,u in zip(z,y)))
        slots[a].append(z);z=tuple(t+u for t,u in zip(z,v))
    return z,D
def audit(name,src):
    n,ar,avoid,base=arrowdata(name)
    tab={key(tuple(tuple(v)for v in loads(k)),n):w for k,w in src.items()}
    assert len(tab)==len(src)
    active=set();done={};stats=[0,0]
    def rec(R):
        if R in done:return done[R]
        assert R not in active;active.add(R)
        assert R in tab and not any(has(R,f,n)for f in avoid)
        w,D=walk(ar,tab[R],n);assert has(R,w,n);dpt=0
        for d in D:
            assert not has(R,d,n)
            child=key(R+(d,),n);assert child!=R
            if any(has(child,f,n)for f in avoid):stats[0]+=1
            else:stats[1]+=1;dpt=max(dpt,1+rec(child))
        done[R]=dpt;active.remove(R);return dpt
    h=rec(key(base,n));assert set(done)==set(tab)
    return len(done),h,*stats
def sharp():
    n,A,_,_=arrowdata('0000111111');w=(1,33,33**2);M=16*sum(w)+1
    tot,D=walk(A,list(data['0000111111']['[]']),n)
    assert not any(tot)
    assert all(sum(x*y for x,y in zip(v,w))%M for v in D)
    # Direct walks in a concrete finite lifted graph; translation and S4 transitivity on
    # the base are not conflated: start at all four layers at coordinate zero.
    arcs={i:[] for i in V}
    for a,b,v,_ in A:arcs[a].append((b,sum(t*u for t,u in zip(v,w))%M))
    for root in V:
        def dfs(i,g,vis,md):
            for j,step in arcs[i]:
                y=(j,(g+step)%M)
                if y==(root,0) and md in (4,8):raise AssertionError
                if md<8 and y not in vis:dfs(*y,vis|{y},md+1)
        dfs(root,0,{(root,0)},1)
if __name__=='__main__':
    shapes();res=[audit(n,x)for n,x in data.items()]
    assert sum(x[0]for x in res)==109 and max(x[1]for x in res)==4
    sharp();print('PASS 179/15 shapes, 109 cells, depth four; invoked terminal/recursive collisions:',sum(x[2]for x in res),sum(x[3]for x in res))
