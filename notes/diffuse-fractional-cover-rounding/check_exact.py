"""Exact diagnostics; the written minimax/asymptotic proofs remain necessary."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import random


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def blocks_of(edges):
    blocks = {}
    for i, edge in enumerate(edges):
        for v in edge:
            blocks.setdefault(v, set()).add(i)
    return {v: frozenset(b) for v,b in blocks.items()}


def audit_family(edges):
    require(all(edges) and len(set(edges)) == len(edges), 'nonempty/simple')
    require(all(a & b for a,b in combinations(edges,2)), 'intersecting')
    return max(map(len,edges)), max(map(len,blocks_of(edges).values()))


def certificate(edges, weights, D):
    blocks = blocks_of(edges)
    require(all(x >= 0 for x in weights.values()), 'nonnegative primal')
    require(all(v in blocks for v in weights), 'known primal coordinates')
    require(all(sum((weights.get(v,F(0)) for v in e),F(0)) == 1 for e in edges),
            'exact primal tiling')
    require(all(len(b) <= D for b in blocks.values()), 'uniform dual feasible')
    require(sum(weights.values(),F(0)) == F(len(edges),D), 'matching objectives')
    require(all(len(blocks[v]) == D for v,x in weights.items() if x),
            'degree-D support')


def affine_three(n):
    points = tuple(product(range(3),repeat=n))
    directions = [d for d in points if any(d) and next(a for a in d if a) == 1]
    lines = []
    classes = []
    for d in directions:
        unique = set()
        for p in points:
            line = frozenset(tuple((a+t*b)%3 for a,b in zip(p,d)) for t in range(3))
            unique.add(line)
        ids=[]
        for line in sorted(unique,key=lambda a:sorted(a)):
            ids.append(len(lines)); lines.append(line)
        classes.append(ids)
    edges = tuple(frozenset(('line',j) for j,L in enumerate(lines) if p in L) for p in points)
    return edges, classes


def repair(edges, removed, D):
    blocks = blocks_of(edges)
    require(all(len(blocks[v]) == D for v in removed), 'removed degree D')
    out = [set(e-removed) for e in edges]
    for v in removed:
        labels=sorted(blocks[v])
        groups=[set(labels[i::3]) for i in range(3)]
        require(all(groups), 'three nonempty groups')
        for g,group in enumerate(groups):
            z=('repair',v,g)
            for i in blocks[v]-group:
                out[i].add(z)
    out = tuple(frozenset(e) for e in out)
    L = max(len(e & removed) for e in edges)
    r,d = audit_family(edges)
    rr,dd = audit_family(out)
    require(rr <= r+L and dd <= D, 'repair rank/degree')
    require(all(len(e2) == len(e)+len(e & removed) for e,e2 in zip(edges,out)),
            'exact repair sizes')
    require(all(2 <= len(b) < D for v,b in blocks_of(out).items() if v not in blocks),
            'new degree below D')
    require(all(blocks_of(out)[v] == b for v,b in blocks.items() if v not in removed),
            'retained original incidences')
    require(not (set(blocks_of(out)) & removed), 'removed support absent')
    return out,L


def check_local(edges, weights, S, D):
    blocks = blocks_of(edges)
    r = max(map(len,edges)); m = len(edges)
    M = max(weights.values(),default=F(0))
    restrictions = Counter()
    for v,b in blocks.items():
        A = b & S
        if len(A) >= 2:
            restrictions[A] += weights.get(v,F(0))
    for p in S:
        codegs = sum(sum(p in b and q in b for b in blocks.values()) for q in S-{p})
        require(codegs <= (D-1)*r-m+len(S), 'actual local pair budget')
        load = sum((x for A,x in restrictions.items() if p in A),F(0))
        require(load <= M*((D-1)*r-m+len(S)), 'actual weighted local budget')
    lam = max((len(a & b & c) for a,b,c in combinations(edges,3)),default=0)
    eta = sum((x for A,x in restrictions.items() if len(A)>=3),F(0))
    require(eta <= len(tuple(combinations(S,3)))*M*lam, 'higher-coordinate budget')
    # An explicit valid matching distribution whenever the total is <=1.
    total = sum(restrictions.values(),F(0))
    if total <= 1:
        distribution = [(x,(A,)) for A,x in restrictions.items() if x]
        distribution.append((1-total,()))
        check_distribution(restrictions, distribution)


def check_distribution(target, distribution):
    require(sum((p for p,_ in distribution),F(0)) == 1, 'probability total')
    expectation = Counter()
    for prob, matching in distribution:
        require(prob >= 0 and all(len(A)>=2 for A in matching), 'probability/support')
        require(all(not (a & b) for a,b in combinations(matching,2)), 'disjoint matching')
        for A in matching:
            expectation[A] += prob
    require(all(expectation[A] == target.get(A,F(0)) for A in expectation.keys() | target.keys()),
            'matching expectation')


def main():
    scalar=0
    for D in range(3,16):
        K=D*(D-2)
        chi=F(D-1)-F(2,3*K+2*(D-1))
        sigma=F(D*(D-2),D-1)
        require(sigma < chi < D-1, 'threshold order')
        for r in range(2,101):
            for m in range(1,(D-1)*r+2):
                gap=(D-1)*m-D*(D-2)*r-D
                if gap<=0: continue
                cap=F(K,gap)
                require(F((D-2)*r+1,D-1) < F(m,D), 'strict finite branch')
                for L in (0,1,2,5):
                    if gap > K*L:
                        require(F((D-2)*(r+L)+1,D-1)<F(m,D), 'repair margin')
                M=cap+F(1,1000)
                L=(1/M).numerator//(1/M).denominator
                require(K*L<gap,'minimax contradiction margin')
                N=(gap+K-1)//K
                rounded=F(1,N)
                require(rounded<=cap,'rounded cap improvement')
                Mr=rounded+F(1,1000)
                Lr=(1/Mr).numerator//(1/Mr).denominator
                require(K*Lr<gap,'rounded minimax contradiction margin')
                scalar+=1
        for delta in (F(0), F(D-1)-chi, (F(D-1)-chi)/2):
            C=F(K)/(1-(D-1)*delta)
            require((C*delta < F(2,3)) == (delta < F(D-1)-chi), 'threshold algebra')
    require(F(2)-F(2,13)==F(24,13) and F(3)-F(2,30)==F(44,15),'named thresholds')
    print(f'{scalar} exact scalar margin/threshold diagnostics PASS')

    edges,classes=affine_three(3)
    r,D=audit_family(edges); m=len(edges)
    uniform={v:F(1,r) for v in blocks_of(edges)}
    certificate(edges,uniform,D)
    concentrated={('line',j):F(1) for j in classes[0]}
    certificate(edges,concentrated,D)
    gap=(D-1)*m-D*(D-2)*r-D
    cap=F(D*(D-2),gap)
    require(max(uniform.values())<=cap<max(concentrated.values()),'existential/every-optimum distinction')
    removed=frozenset(concentrated)
    changed,L=repair(edges,removed,D)
    require(gap>D*(D-2)*L,'positive repair margin')
    avoiding={('line',j):F(1) for j in classes[1]}
    certificate(changed,avoiding,D)
    averaged={v:(concentrated.get(v,F(0))+avoiding.get(v,F(0)))/2 for v in concentrated.keys() | avoiding.keys()}
    certificate(edges,averaged,D)
    require(max(averaged.values())<max(concentrated.values()),'explicit peak reduction')
    print(f'Affine certificate and parallel-class repair: m={m}, r={r}, gap={gap}, cap={cap} PASS')

    rng=random.Random(20261007)
    # Remove several arbitrary full-degree coordinates, including an entire direction.
    verts=tuple(blocks_of(edges))
    for size in (1,2,5,13,35):
        repair(edges,frozenset(rng.sample(verts,size)),D)
    smaller,_=affine_three(2)
    smallweights={v:F(1,4) for v in blocks_of(smaller)}
    for mask in range(1<<9):
        S=frozenset(p for p in range(9) if mask>>p & 1)
        check_local(smaller,smallweights,S,3)
    for _ in range(80):
        S=frozenset(rng.sample(range(m),rng.randrange(1,7)))
        check_local(edges,uniform,S,D)
    print('Five independent repair replays and 592 exact local incidence budgets PASS')

    higher=0
    for degree in range(3,13):
        pts=tuple(range(degree+3))
        allblocks=tuple(combinations(pts,degree))
        original=tuple(frozenset(('subset',j) for j,b in enumerate(allblocks) if i in b) for i in pts)
        vertices=tuple(blocks_of(original))
        for size in (1,len(vertices)//4,len(vertices)):
            repair(original,frozenset(rng.sample(vertices,size)),degree)
            higher+=1
    require(F(1,4)*((3-1)*13-27+3) == F(2,3)*(1-F(1,4)),
            'finite h=3 polytope criterion at equality')
    print(f'{higher} higher-degree three-complement repairs and exact finite polytope criterion PASS')

    # A true large-pair/small-triple family, not a floating-point experiment.
    t=2
    extended=[set(e) for e in edges]
    for l in range(t):
        z=('pairclone',l); extended[0].add(z); extended[1].add(z)
        for i in range(2,m): extended[i].add(('private',i,l))
    extended=tuple(frozenset(e) for e in extended)
    rr,dd=audit_family(extended)
    certificate(extended,uniform,D)
    require(rr==r+t and dd==D and len(extended[0]&extended[1])==t+1,'cloned pair')
    require(max(len(a&b&c) for a,b,c in combinations(extended,3))==1,'small triple')
    print('Pair-cloned optimum: pair intersection 3, triple intersection 1 PASS')

    # K5 pair mass + a rare higher subset; explicit convex distribution.
    S=frozenset(range(5)); pairs=[frozenset(p) for p in combinations(S,2)]
    target={p:F(3,20) for p in pairs}; target[S]=F(1,100)
    matchings=[]
    for unmatched in S:
        rest=sorted(S-{unmatched}); a=rest[0]
        for b in rest[1:]:
            other=frozenset(set(rest)-{a,b})
            matchings.append((frozenset((a,b)),other))
    distribution=[(F(1,20),mat) for mat in matchings]+[(F(1,100),(S,)),(F(6,25),())]
    check_distribution(target,distribution)
    for h in range(3,80,2):
        require(F(h,3)<=F(h-1,2),'odd-set degree condition')
    # Above 2/3 the triangle demonstrates that vertex loads <=1 alone fail.
    triangle={frozenset(p):F(2,5) for p in combinations(range(3),2)}
    require(max(sum(x for A,x in triangle.items() if p in A) for p in range(3))<1,'triangle vertex loads')
    require(sum(triangle.values())>1,'triangle odd-set obstruction')
    # D=2 cannot be included: triangle incidence optimum has positive coordinates.
    degree_two=(frozenset(('a','b')),frozenset(('a','c')),frozenset(('b','c')))
    certificate(degree_two,{v:F(1,2) for v in ('a','b','c')},2)
    require(F(1,2)>F(2*(2-2),3-2),'degree-two diffuse-bound counterexample')
    print('Full local matching distribution and triangle/degree-two negative controls PASS')


if __name__=='__main__':
    main()
