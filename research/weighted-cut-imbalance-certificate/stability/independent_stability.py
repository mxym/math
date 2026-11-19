#!/usr/bin/env python3
"""Independent stability replay, extending the published alternative verifier from #123. Five-edge-mass dual, integer halfspaces in projective coordinates,
pool-adjacent-violators majorizer and branch-and-bound exact sign integration."""
import sys, json, hashlib, math
from itertools import product
from pathlib import Path
from fractions import Fraction as F
from functools import cache
from itertools import combinations
from collections import Counter
def need(b, msg='certificate check failed'):
    if not b: raise ValueError(msg)
def isint(i):return type(i) is int
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def independent_solve(cols,target):
    # Exactly one solution for independent columns; use five full edge types, not a fixed choice of three eliminated coordinates.
    n=len(cols);M=[[F(col[i]) for col in cols]+[F(t)] for i,t in enumerate(target)]
    for j in range(n):
        k=next((k for k in range(j,len(M)) if M[k][j]),None)
        need(k is not None,'dependent columns')
        M[k],M[j]=M[j],M[k];v=M[j][j];M[j]=[a/v for a in M[j]]
        for i in range(len(M)):
            if i!=j and M[i][j]:
                x=M[i][j];M[i]=[a-x*b for a,b in zip(M[i],M[j])]
    L=[M[i][-1] for i in range(n)]
    need(all(dot((col[i] for col in cols),L)==t for i,t in enumerate(target)))
    return L
@cache
def row(k,idx):
    # slots are HH' (inside ranks 2..k), H'1, outside-outside, outside-1, outside-H'.
    b=k-1;nc=(b+1)*13
    if idx<nc:
        r,j=divmod(idx,13);p=F(j,12)
        # Without-replacement directed calculation: opposite-side endpoints in r*(b-r) ways, twice.
        h=F(2*r*(b-r),b*(b-1)) if b>=2 else 0;t=F(r,b)
        return ((h,t,2*p*(1-p),p,t*(1-p)+(1-t)*p),1)
    v=idx-nc;need(0<=v<5 or (v==5 and b==1))
    return (tuple((-int(i==v) if v!=5 else int(i==0)) for i in range(5)),0)
def plane(k,entry):
    if entry=='max':return (F(0),F(0),F(k))
    if entry=='mass':return (F(2),F(0),F(0))
    need(isinstance(entry,list) and 1<=len(entry)<=3 and all(isint(i) and i>=0 for i in entry) and len(set(entry))==len(entry))
    v=[row(k,i) for i in entry]
    target=(2,2,0,1,1)
    co=independent_solve([t[0] for t in v]+[(1,1,1,1,1),(0,1,0,1,0)],target)
    need(all(x>=0 for x in co[:-2]))
    return co[-2],dot(co[:-2],[t[1] for t in v]),co[-1]
def integral(xs):
    den=math.lcm(*(F(a).denominator for a in xs));ints=[int(den*x) for x in xs]
    g=math.gcd(*ints)
    need(g>0)
    return tuple(i//g for i in ints)
def plane_to_line(p): # homogeneous (wc,wd,w0), inward orientation
    return integral((p[1],p[2],p[0]))
def cross(h,t):return (h[1]*t[2]-h[2]*t[1],h[2]*t[0]-h[0]*t[2],h[0]*t[1]-h[1]*t[0])
def polytope(inequalities):
    # Pairwise boundary intersections, then remove all redundant/non-edge constraints.
    # Bounded parent and intersection ensure this lists every vertex; no polygon clipping.
    V=set();ineq=tuple(set(inequalities))
    for h,t in combinations(ineq,2):
        q=cross(h,t)
        if not q[2]:continue
        g=math.gcd(*q)*(1 if q[2]>0 else -1)
        q=tuple(s//g for s in q)
        if all(dot(q,u)>=0 for u in ineq):V.add(q)
    need(len(V)>=3)
    facets=tuple(h for h in ineq if sum(dot(h,q)==0 for q in V)>=2)
    # sum signed twice-area, ordering the two endpoints of each boundary with inward normals to the left
    area=F(0)
    for h in facets:
        X=[q for q in V if dot(h,q)==0];need(len(X)==2)
        a,b=X
        if (b[0]*a[2]-a[0]*b[2])*h[1]-(b[1]*a[2]-a[1]*b[2])*h[0]<0:a,b=b,a
        area+=F(a[0]*b[1]-a[1]*b[0],a[2]*b[2])
    need(area>0 and len(facets)==len(V))
    return facets,V,area
def projected(Y):
    # Concavify the prefix sequence by averaging increasing adjacent blocks of slopes.
    S=[]
    for x,y in zip(Y,Y[1:]):
        S.append((y-x,1))
        while len(S)>=2 and S[-1][0]*S[-2][1] >= S[-2][0]*S[-1][1]:
            a,i=S.pop();b,j=S.pop();S.append((a+b,i+j))
    a=tuple(x/n for x,n in S for _ in range(n));need(len(a)==32 and sum(a)==2 and min(a)>=0)
    need(all(x>=y for x,y in zip(a,a[1:])))
    v=0
    for k,t in enumerate(a,1):
        v+=t;need(v>=Y[k])
    return a
@cache
def signed_integral(a):
    # Group equal scaled weights. Recursively evaluate positive-part moments exactly, replacing
    # entire subtrees by zero/conditional mean once the residual cannot change sign.
    actual=[x for x in a if x];scale=math.lcm(*(x.denominator for x in actual))
    nums=[int(x*scale) for x in actual];B=sorted(Counter(nums).items(),reverse=True)
    m=len(B);rems=[0]*(m+1);N=[0]*(m+1);opts=[]
    for J in reversed(range(m)):
        x,l=B[J];rems[J]=rems[J+1]+x*l;N[J]=N[J+1]+l
    for x,l in B:opts.append(tuple(((l-2*j)*x,math.comb(l,j)) for j in range(l+1)))
    @cache
    def pos(j,v):
        if v>=rems[j]:return v*(1<<N[j])
        if v<=-rems[j]:return 0
        return sum(h*pos(j+1,v+delta) for delta,h in opts[j])
    # E|Z|=2 E Z_+ for a symmetric centered variable.
    val=F(2*pos(0,0),scale*(1<<len(actual)));pos.cache_clear()
    return val
def microchecks():
    for a0 in product(range(1,4),repeat=5):
        a=tuple(F(x,19) for x in a0)
        exact=sum(abs(dot(s,a)) for s in product((-1,1),repeat=5))/32
        need(signed_integral(a)==exact,'failed brute sign sum')
    # Independently enumerate random cuts on a graph having all five edge types,
    # including every size-r subset of B and every outside Bernoulli pattern.
    n=6;idx=[(i,j) for i in range(n) for j in range(i+1,n)]
    w={(i,j):(2*i+5*j+1)%11+1 for i,j in idx}
    for k in range(2,6):
        b=k-1
        edges=[sum(w[i,j] for i,j in idx if pred(i,j)) for pred in (
            lambda i,j:0<i<j<k, lambda i,j:i==0 and j<k,lambda i,j:k<=i,
            lambda i,j:i==0 and k<=j,lambda i,j:0<i<k<=j)]
        for r in range(k):
            for u in range(13):
                p=F(u,12);avg=0
                for mask in product((0,1),repeat=n-1):
                    if sum(mask[:b])!=r:continue
                    s=(0,)+mask;tot=sum(w[i,j] for i,j in idx if s[i]!=s[j]);out=sum(mask[b:])
                    avg+=F(tot,math.comb(b,r))*p**out*(1-p)**(n-k-out)
                need(avg==dot(edges,row(k,r*13+u)[0]),'failed explicit random cuts')
    print('microchecks: 243 direct sign expectations, 182 explicit random-cut laws')
def main(file):
    raw=Path(file).read_bytes()
    need(hashlib.sha256(raw).hexdigest()=='353673afb1e06fdf1529ec8d81e518e688b4ded7d750f079f8499ccd154a0b9d','wrong certificate')
    J=json.loads(raw);need(set(J)=={'bounds','cells','version'} and J['version']==1 and len(J['bounds'])==30)
    P={k:[plane(k,u) for u in lst] for k,lst in enumerate(J['bounds'],2)}
    def get(k,i):
        need(isint(k) and 2<=k<=31 and isint(i) and 0<=i<len(P[k]));return P[k][i]
    base=[(2,0,-1),(-3,0,2),(0,1,0),(0,-3,2)]
    for i in range(13):
        p=F(i,12);g=2*p*(1-p);base.append(plane_to_line((-g,1,g-p)))
    H,V,area=polytope(base);cover=0;ls=Counter();keys=Counter();gaps=[];margins=[];inc=0
    @cache
    def classify(q,I):
        w=(1,F(q[0],q[2]),F(q[1],q[2]))
        a=projected([F(0),w[2]]+[dot(get(k,i),w) for k,i in enumerate(I,2)]+[F(2)])
        B=(15*w[1]-6)/4;need(B>0)
        # Certify strict corners directly vs the target B-eps, rather than the old B^2.
        eps=F(1,100000)
        if B>eps and dot(a,a)<=(B-eps)**2:
            keys['square']+=1;return 0
        exact=signed_integral(a);need(B>=exact)
        if exact<B:
            need(B-exact>=eps,'strict slack below fixed threshold')
            gaps.append(B-exact);keys['strict exact']+=1;return 0
        b=tuple(x for x in a if x)
        n=len(b);need((n,w[1]) in ((3,F(2,3)),(5,F(3,5))))
        # Worst possible signed sum on the majority (positive side) is obtained by
        # placing the floor(n/2) largest weights in the minority.
        margin=sum(b)-2*sum(b[:n//2]);need(margin>=F(23,65))
        margins.append(margin);keys['tight']+=1;return n
    def visit(node,H,V,area):
        nonlocal inc,cover
        if len(node)==1:
            I=tuple(node[0]);need(len(I)==30);inc+=len(V);cover+=area
            ranks=set(classify(q,I) for q in V)-{0};need(len(ranks)<=1,'mixed leaf')
            ls[next(iter(ranks),0)]+=1;return
        need(len(node)==3)
        k,i,j=node[0];l=plane_to_line([x-y for x,y in zip(get(k,i),get(k,j))])
        left=polytope(H+(l,));right=polytope(H+(tuple(-x for x in l),))
        need(left[-1]+right[-1]==area);visit(node[1],*left);visit(node[2],*right)
    visit(J['cells'],H,V,area)
    need(cover==area==F(130792,765765) and inc==3791 and sum(ls.values())==957)
    need(min(margins)==F(23,65))
    print('number of valid prefix planes:',sum(map(len,P.values())))
    print('leaf types (0=strict only):',sorted(ls.items()),'corner incidences:',inc)
    print('distinct tests:',sorted(keys.items()),'minimum majority margin:',min(margins))
    print('all strict corners have B-K >= 1/100000; least strict gap requiring exact sign sum:',min(gaps))
    # Uniform explicit constant from independent proof. D = tau/delta, E = |c-c0|/delta.
    E=F(100000,6); D=F(8,3)*(1+12+F(5,8)*100000)
    need(max(400000,191*D+405*E,10*D+9*E,110)<40000000)
    # A second, incidence-matrix recovery: internal balanced cuts on K3/K5 form an 
    # invertible system. Account for outside-incidence O(tau) before inverting.
    for r,t in [(3,1),(5,2)]:
        pairs=list(combinations(range(r),2));S=list(combinations(range(r),t))
        M=[[int((u in side)!=(v in side)) for side in S] for u,v in pairs]
        cols=[independent_solve(M,[int(i==j) for i in range(len(S))]) for j in range(len(S))]
        print('inverse internal balanced-cut map induced 1-norm, r=%s:'%r,max(sum(map(abs,c)) for c in cols))
    print('explicit uniform coarse L=40000000; PASS')
if __name__=='__main__':main(sys.argv[1])
