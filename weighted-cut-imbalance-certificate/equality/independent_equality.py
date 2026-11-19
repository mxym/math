#!/usr/bin/env python3
"""Independent replay. Five-edge-mass dual, integer halfspaces in projective coordinates,
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
    microchecks()
    raw=Path(file).read_bytes();need(hashlib.sha256(raw).hexdigest()=='353673afb1e06fdf1529ec8d81e518e688b4ded7d750f079f8499ccd154a0b9d','changed frozen certificate')
    D=json.loads(raw);need(set(D)=={'bounds','cells','version'} and D['version']==1)
    bb=D['bounds'];need(len(bb)==30)
    P={k:[plane(k,i) for i in lst] for k,lst in enumerate(bb,2)}
    def get(k,i):
        need(isint(k) and 2<=k<=31 and isint(i) and 0<=i<len(P[k]));return P[k][i]
    base=[(2,0,-1),(-3,0,2),(0,1,0),(0,-3,2)]
    for i in range(13):
        p=F(i,12);g=2*p*(1-p);base.append(plane_to_line((-g,1,g-p)))
    H,V,orig=polytope(base);c=Counter();zarea=0;zeropoints=Counter()
    @cache
    def evaluate(q,choices):
        w=(1,F(q[0],q[2]),F(q[1],q[2]))
        Y=[F(0),w[2]]+[dot(get(k,i),w) for k,i in enumerate(choices,2)]+[F(2)]
        a=projected(Y);budget=(15*w[1]-6)/4;need(0<budget<=1)
        pos=tuple(x for x in a if x)
        if dot(a,a)<=budget*budget:
            # Strict Jensen on the nonconstant absolute signed sum. Its square
            # changes between the all-plus signs and a flip of a single positive.
            need(len(pos)>=2 and (sum(pos)-2*pos[-1])**2<sum(pos)**2)
            c['strict-square']+=1;return
        val=signed_integral(a);need(val<=budget,('bad absolute first moment',q,choices))
        if val==budget:
            zeropoints[(w[1:],pos)]+=1
            c['tight-exact']+=1
        else:c['strict-exact']+=1
    def visit(node,H,V,area):
        nonlocal zarea
        need(type(node) is list)
        if len(node)==1:
            I=node[0];need(type(I) is list and len(I)==30)
            for q in V:evaluate(q,tuple(I))
            c['leaves']+=1;c['vertices']+=len(V);zarea+=area;return
        need(len(node)==3)
        k,i,j=node[0];u=get(k,i);v=get(k,j)
        l=plane_to_line([a-b for a,b in zip(u,v)])
        s=polytope(H+(l,));t=polytope(H+(tuple(-x for x in l),));need(s[2]+t[2]==area)
        c['internal']+=1;visit(node[1],*s);visit(node[2],*t)
    visit(D['cells'],H,V,orig)
    need(orig==zarea and c['leaves']==c['internal']+1)
    print('five-coordinate certified affine bounds:',sum(map(len,P.values())))
    print('all closed cells and their vertices:',dict(c));print('twice-area:',orig)
    expected={
      ((F(2,3),F(2,3)),(F(2,3),)*3),
      ((F(3,5),F(2,5)),(F(2,5),)*5),
      ((F(3,5),F(107,260)),(F(107,260),)*3+(F(199,520),)*2)}
    need(set(zeropoints)==expected,'incomplete or unexpected tight support type')
    need(c['strict-exact']==1395 and c['tight-exact']==16 and c['strict-square']==2318)
    need(orig==F(130792,765765) and (c['internal'],c['leaves'],c['vertices'])==(956,957,3791))
    for (v,pos),m in sorted(zeropoints.items()):
        # Direct signed influences, including 2 inert coordinates. This checks not
        # just signed expectation but the one-cube maximizer and its subgradient.
        S=list(product((-1,1),repeat=len(pos)+2))
        signs=[sum(a*b for a,b in zip(e,pos)) for e in S]
        votes=[sum(e[:len(pos)]) for e in S]
        need(all(z*t>0 for z,t in zip(signs,votes)),'nontrivial tie or different sign function')
        g=tuple(F(sum(e[j]*(1 if v>0 else -1) for v,e in zip(votes,S)),len(S)) for j in range(len(pos)+2))
        x=F(math.comb(len(pos)-1,(len(pos)-1)//2),2**(len(pos)-1))
        need(g==(x,)*len(pos)+(0,0) and x*2==(15*v[0]-6)/4)
        print('tight corner/vector: ',v,pos,'multiplicity in distinct (corner, choice) keys:',m,'active influence:',x)
    graphchecks()
    print('PASS')
def graphchecks():
    # Invert the entire system of (singleton or doubleton) balanced cuts as a
    # linear map on edges, independently of degree reconstruction in the proof.
    for n,t in ((3,1),(5,2)):
        E=list(combinations(range(n),2)); ss=list(combinations(range(n),t))
        cols=[[int((i in side)!=(j in side)) for side in ss] for i,j in E]
        co=independent_solve(cols,[F(t*(n-t),math.comb(n,2))]*len(ss))
        need(co==[F(1,math.comb(n,2))]*len(E),'singular/wrong rigid clique solution')
    # Exhaustive small weighted configurations: allow zero, one or two per
    # pair of a labeled five-set (all supports, including isolated vertices).
    # Scale the inequality by 2^5 to avoid fraction overhead.
    edges=list(combinations(range(5),2))
    signs=list(product((-1,1),repeat=5)); positives=[]
    masks=[[j for j,(u,v) in enumerate(edges) if e[u]!=e[v]] for e in signs[::2]]
    for w in product(range(3),repeat=len(edges)):
        W=sum(w)
        if W==0:continue
        D=[0]*5
        for a,(i,j) in zip(w,edges):D[i]+=a;D[j]+=a
        C=max(sum(w[j] for j in S) for S in masks)
        L1=sum(abs(sum(x*y for x,y in zip(D,e))) for e in signs)
        slack=32*(15*C-6*W)-4*L1
        need(slack>=0,'counterexample in exact enumeration')
        if not slack:
            active={v for k,(i,j) in enumerate(edges) if w[k] for v in (i,j)}
            s=len(active); vals={a for a in w if a}
            need(s in (3,5) and len(vals)==1 and sum(bool(a) for a in w)==s*(s-1)//2)
            positives.append((s,max(w)))
    need(Counter(positives)=={(3,1):10,(3,2):10,(5,1):1,(5,2):1})
    print('complete balanced cut systems uniquely solved: 3/3 ranks and 10/10 ranks')
    print('59048 nonzero labeled 5-vertex graphs, per-pair weights 0,1,2:',sorted(Counter(positives).items()))

if __name__=='__main__':
    main(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'general-proof'/'certificate.json')
