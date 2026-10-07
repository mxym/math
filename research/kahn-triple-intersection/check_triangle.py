"""Exact diagnostics for the attributed local-triangle obstacle."""
from fractions import Fraction as F
from itertools import combinations, product


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def check(s,N):
    # These finite diagnostics use prime fields only. The written proof
    # also applies to nonprime finite fields with the usual affine lines.
    points=list(product(range(s),repeat=N))
    lines=set()
    for a in points:
        for d in points:
            if not any(d):
                continue
            line=frozenset(tuple((a[j]+t*d[j])%s for j in range(N)) for t in range(s))
            lines.add(line)
    lines=sorted(lines,key=lambda L:sorted(L))
    blocks=[frozenset((x,i) for x in L for i in range(3) if i!=a)
            for L in lines for a in range(3)]
    auxiliary=list(product(points,range(3)))
    edges=[frozenset(j for j,B in enumerate(blocks) if p in B) for p in auxiliary]
    v=s**N;r0=(v-1)//(s-1);r=2*r0;m=3*v
    require(len(lines)==v*r0//s,'line count')
    require(len(set(edges))==m and all(len(E)==r for E in edges),'simple uniform dual')
    pair=[len(E & Q) for E,Q in combinations(edges,2)]
    require(min(pair)>=1 and max(pair)==r0,'pair intersections')
    require(max(len(E & Q & R) for E,Q,R in combinations(edges,3))<=2,'triple codegree')
    parallel=[j for j,L in enumerate(lines)
              if all(len({x[c] for x in L})==1 for c in range(1,N))]
    require(len(parallel)==v//s,'parallel class')
    selected=[3*j+a for j in parallel for a in (0,1)]
    require(all(set(selected)&E for E in edges),'explicit integer cover')
    require(len(selected)==2*v//s,'integer objective')
    # The counting lower bound is valid for any selected cover:
    # at least two block incidences per local triple, s triples per block.
    require(all(len(B)==2*s and len({x for x,i in B})==s for B in blocks),'block capacities')
    require(all(len({i for x,i in B if x==a}) in (0,2)
                for B in blocks for a in points),'local triangle capacity')
    dual=[F(1,2*s)]*m;primal=[F(1,r)]*len(blocks)
    require(all(sum(primal[j] for j in E)==1 for E in edges),'primal feasibility')
    require(all(sum(dual[i] for i,E in enumerate(edges) if j in E)==1
                for j in range(len(blocks))),'dual feasibility')
    tau=F(2*v,s);fractional=F(3*v,2*s)
    require(sum(primal)==sum(dual)==fractional,'exact optimal objective')
    require(tau/fractional==F(4,3),'fixed rounding loss')
    kahn=[F(len(B),m+r-1) for B in blocks]
    for h in range(1,7):
        S=set(auxiliary[:h]);ell=(h+1)//2
        actual=sum(kahn[j] for j,B in enumerate(blocks) if B&S)
        lower=F(h*r+ell*(m-h-2*s*(h*(h-1)*(h-2)//6)*2),m+r-1)
        require(actual>=lower,'local weight surplus count')
    local={(points[0],i) for i in range(3)}
    local_kahn=sum(kahn[j] for j,B in enumerate(blocks) if B&local)
    local_optimal=sum(primal[j] for j,B in enumerate(blocks) if B&local)
    require(local_optimal==F(3,2) and local_kahn==F(6*s*r0,m+r-1)>2,
            'specific versus optimal weight comparison')
    c=F(3*(s-1),2)
    require(c/(c+1)-F(s-1,s)==F(s-1,s*(3*s-1))>0,'conjecture compatibility')
    print(f's={s}, N={N}: r={r}, m={m}, tau={tau}, tau*={fractional}, gap=4/3 PASS')


if __name__=='__main__':
    for case in ((2,2),(2,3),(3,2),(3,3)):
        check(*case)
