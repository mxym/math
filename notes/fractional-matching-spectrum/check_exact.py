"""Exact bounded-packing replay; no optimizer or solver is imported.

ancestor_exact.py is the byte-identical construction helper frozen in
public c5255aa, explicitly reused rather than counted as new code.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from random import Random
from ancestor_exact import affine_design, ramp


def require(ok,message):
    if not ok:
        raise RuntimeError(message)


def f(n):
    return F(n,n+1)


def psi(c):
    if c<=1:
        return c/2
    a=c.numerator//c.denominator
    return max(f(a),c/F(a+2))


def h(c):
    a=c.numerator//c.denominator
    return f(a)+(c-a)/((a+1)*(a+2))


def spectrum(s,c):
    require(s>=1 and c>=0,'spectrum domain')
    if s==1:
        return psi(c)
    Q=c.numerator//c.denominator
    theta=c-Q
    values=[]
    for a in range(Q+1):
        b,t=divmod(Q-a,s-1)
        values.append(psi(a+theta)+(s-1-t)*f(b)+t*f(b+1))
    return max(values)


def matching_number(edges):
    conflict=[]
    for E in edges:
        conflict.append(sum(1<<j for j,G in enumerate(edges) if E&G))
    @lru_cache(None)
    def visit(mask):
        if not mask:
            return 0
        i=(mask&-mask).bit_length()-1
        return max(visit(mask&~(1<<i)),1+visit(mask&~conflict[i]))
    return visit((1<<len(edges))-1)


def check_family(edges,y,s,primal=None,r=None):
    require(len(edges)==len(y) and len(set(edges))==len(edges),'simple domain')
    require(all(E for E in edges) and all(z>=0 for z in y),'nonempty/nonnegative')
    r=r if r is not None else max(map(len,edges),default=2)
    require(r>=2 and all(len(E)<=r for E in edges),'rank')
    loads=Counter()
    for E,z in zip(edges,y):
        for v in E:
            loads[v]+=z
    require(all(z<=1 for z in loads.values()),'vertex feasibility')
    Y=sum(y,F(0)); m=len(edges)
    if primal is not None:
        vertices=set().union(*edges) if edges else set()
        require(set(primal)==vertices and all(z>=0 for z in primal.values()),'primal domain')
        require(all(sum(primal[v] for v in E)>=1 for E in edges),'primal feasibility')
        require(sum(primal.values())==Y,'exact primal/dual optimum')
    remaining=set(range(m));groups=[];anchors=[]
    while remaining:
        P=max(remaining,key=lambda i:(y[i],-i))
        G=sorted(i for i in remaining if edges[i]&edges[P])
        require(P in G and G,'anchor belongs to group')
        remaining.difference_update(G);groups.append(G);anchors.append(P)
        b=y[P]; t=len(G); Z=sum((y[i] for i in G),F(0))
        require(all(y[i]<=b for i in G),'actual maximum anchor')
        require(all(y[i]+b<=1 for i in G if i!=P),'anchor pair constraint')
        require(Z<=r-(r-1)*b,'anchored weighted star')
        require(Z<=F(t,2) if t>=2 else Z<=1,'anchored half/single bound')
        bins={v:[] for v in edges[P]}
        for i in G:
            if i!=P:
                bins[min(edges[i]&edges[P])].append(y[i])
        require(sum(map(len,bins.values()))==t-1 and sum(sum(B) for B in bins.values())==Z-b,
                'genuine anchored partition')
        for k in range(2,13):
            bound=max(F((k-1)*r+1,k),F(t,k+1))
            require(Z<=bound,'anchored finite frontier')
            if F(1,k+1)<b<=F(1,k):
                B=1-k*b; p=(k+1)*b-1
                for weights in bins.values():
                    W=sum(weights);ell=len(weights)
                    require(W<=1-b and W<=ell*b and W-B*ell<=(k-1)*p,'anchored signed bin')
        require(Z<=r*psi(F(t,r))+F(1,2),'anchored curve/error')
    require(sorted(i for G in groups for i in G)==list(range(m)),'group partition')
    require(all(not(edges[P]&edges[Q]) for P,Q in combinations(anchors,2)),'disjoint anchors')
    require(len(groups)<=s,'packing budget')
    require(Y<=r*spectrum(s,F(m,r))+F(s,2),'finite bounded-packing law')
    require(Y<=r*s*h(F(m,r*s))+F(s,2),'concave relaxation')
    return r,m,Y,len(groups)


def pair_design(n):
    blocks=list(combinations(range(n),2))
    edges=[frozenset(i for i,T in enumerate(blocks) if a in T) for a in range(n)]
    return edges,[F(1,2)]*n,{i:F(1,n-1) for i in range(len(blocks))}


def private_pad(data,R):
    edges,y,primal=data
    fresh=max(primal,default=-1)+1
    out=[]
    for E in edges:
        extra=R-len(E)
        require(extra>=0,'common-rank padding')
        new=frozenset(range(fresh,fresh+extra))
        primal.update({v:F(0) for v in new});fresh+=extra
        out.append(E|new)
    return out,y,primal


def union_components(components):
    edges=[];y=[];primal={};fresh=0
    for E,w,z in components:
        vertices=sorted(set().union(*E))
        mapping={v:fresh+j for j,v in enumerate(vertices)}
        fresh+=len(vertices)
        require(all(A&B for A,B in combinations(E,2)),'intersecting component')
        edges.extend(frozenset(mapping[v] for v in A) for A in E)
        y.extend(w);primal.update({mapping[v]:a for v,a in z.items()})
    return edges,y,primal


def main():
    comparisons=0
    for D in (1,2,3,4,6):
        Mmax=12*D
        grid=[psi(F(i,D)) for i in range(Mmax+1)]
        previous=[F(0)]+[None]*Mmax
        for s in range(1,6):
            current=[]
            for M in range(Mmax+1):
                current.append(max(previous[M-i]+grid[i] for i in range(M+1)
                                   if previous[M-i] is not None))
                c=F(M,D);value=spectrum(s,c)
                require(value==current[M],'closed formula versus independent grid convolution')
                gap=s*h(c/s)-value
                require(0<=gap<=F(c.numerator%c.denominator,2*c.denominator),'concave finite gap')
                require((gap>0)==(c>s and c.denominator>1),'strict gap distinction')
                comparisons+=1
            previous=current
    print(f'{comparisons} rational spectrum/grid-convolution and gap diagnostics PASS')
    for c,value in ((F(3),F(7,6)),(F(7,2),F(7,6)),(F(15,4),F(5,4))):
        require(spectrum(2,c)==value,'fixed spectral values')
    print('Three exact two-packing spectrum values PASS')
    for s in (1,2,3,7):
        R=5
        edges=[frozenset(range(i*R,(i+1)*R)) for i in range(s)]
        primal={v:F(int(v%R==0)) for E in edges for v in E}
        r,m,Y,l=check_family(edges,[F(1)]*s,s,primal)
        require(Y==r*spectrum(s,F(m,r))+F(s,2),'optimal universal additive error')
    print('s/2 finite error attained for four disjoint-edge certificates PASS')
    components=[pair_design(14) for _ in range(3)]
    data=union_components(components)
    r,m,Y,l=check_family(*data[:2],3,data[2])
    require(Y==r*spectrum(3,F(m,r))+F(3,2),'balanced component finite equality')
    print(f'Balanced components: r={r}, m={m}, nu={l}, tau*={Y}, exact optimum PASS')
    E,w,z,_=affine_design(3,3)
    data=union_components([pair_design(14),(E,w,z)])
    r,m,Y,l=check_family(*data[:2],2,data[2])
    print(f'Mixed design components: r={r}, m={m}, nu={l}, tau*={Y}, exact optimum PASS')
    padded=private_pad((E,w,dict(z)),15)
    data=union_components([pair_design(16),padded])
    r,m,Y,l=check_family(*data[:2],2,data[2])
    print(f'Common-rank padded components: r={r}, m={m}, nu={l}, tau*={Y}, exact optimum PASS')
    star=[frozenset((0,1,2)),frozenset((0,3,4)),frozenset((1,5,6)),frozenset((2,7,8))]
    y=[F(0),F(1),F(1),F(1)]
    require(sum(y)>max(F(4,2),F(4,3)),'nonmaximum anchor negative control')
    primal={v:F(int(v in (0,1,2))) for v in range(9)}
    check_family(star,y,matching_number(star),primal)
    print('Nonintersecting star groups PASS; nonmaximum-anchor overclaim detected PASS')
    rng=Random(20261007);samples=0
    for _ in range(200):
        r=rng.choice((2,3,4));V=rng.choice((7,8,9))
        pool=list(combinations(range(V),r));rng.shuffle(pool)
        edges=[frozenset(T) for T in pool[:rng.randrange(1,13)]]
        raw=[F(rng.randrange(0,6),7) for _ in edges]
        loads=Counter()
        for E,w in zip(edges,raw):
            for v in E:
                loads[v]+=w
        scale=max(F(1),max(loads.values(),default=F(0)))
        y=[w/scale for w in raw]
        nu=matching_number(edges)
        check_family(edges,y,nu)
        samples+=1
    print(f'{samples} exact feasible-vector greedy partitions with exhaustive matching numbers PASS')
    check_family([],[],1,r=2)
    print('Empty-family boundary PASS')


if __name__=='__main__':
    main()
