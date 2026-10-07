"""Exact signed-partition replay and primal/dual construction certificates.

No LP solver or exploratory search is imported. These finite diagnostics
support the universal written proof and partial Lean exports; they do
not establish Wilson's or Kahn's published existence theorems.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def finite_bound(r, m, k):
    return max(F((k-1)*r+1, k), F(m, k+1))


def psi(c):
    if c <= 1:
        return c/2
    a = c.numerator//c.denominator
    return max(F(a, a+1), c/F(a+2))


def check_vector(edges, y, primal=None):
    require(bool(edges) and len(edges) == len(y), 'domain')
    m = len(edges)
    r = max(map(len, edges))
    require(r >= 2 and all(edges), 'rank/nonempty')
    require(len(set(edges)) == m, 'simplicity')
    require(all(E & G for E, G in combinations(edges, 2)), 'intersectingness')
    require(all(w >= 0 for w in y), 'nonnegative weights')
    loads = Counter()
    for E,w in zip(edges,y):
        for v in E:
            loads[v] += w
    require(all(w <= 1 for w in loads.values()), 'dual feasibility')
    Y, b = sum(y), max(y)
    P = edges[y.index(b)]
    require(Y <= r-(r-1)*b, 'rank-weighted star')
    if m >= 2:
        require(Y <= F(m, 2), 'pair bound')
    if primal is not None:
        vertices = set().union(*edges)
        require(set(primal) == vertices and all(z >= 0 for z in primal.values()), 'primal domain')
        require(all(sum(primal[v] for v in E) >= 1 for E in edges), 'primal feasibility')
        require(sum(primal.values()) == Y, 'primal/dual optimum certificate')
    bin_weights = {v: [] for v in P}
    for i,E in enumerate(edges):
        if i != y.index(b):
            bin_weights[min(E & P)].append(y[i])
    require(sum(map(len,bin_weights.values())) == m-1, 'exact assignment count')
    require(sum(sum(W) for W in bin_weights.values()) == Y-b, 'exact assignment mass')
    for k in range(2,13):
        require(Y <= finite_bound(r,m,k), 'finite frontier bound')
        if F(1,k+1) < b <= F(1,k):
            B = 1-k*b
            D = (k-1)*((k+1)*b-1)
            score = F(0)
            for values in bin_weights.values():
                W, ell = sum(values), len(values)
                require(W <= ell*b and W <= 1-b, 'bin feasibility')
                require(W-B*ell <= D, 'signed bin bound')
                score += W-B*ell
            require(score == Y-b-B*(m-1), 'signed score conserved')
            require(score <= r*D, 'signed score summed')
            g = (k-1)*r+1
            affine = m-g+b*((k+1)*g-k*m)
            require(Y <= affine <= finite_bound(r,m,k), 'affine elimination/endpoints')
        A=k*m-(k+1)*((k-1)*r+1)
        if A > 0:
            d=F(m,k+1)-Y
            require(d >= 0, 'strict ramp deficit sign')
            if primal is not None:
                capped=max(Counter(v for E in edges for v in E).values()) <= k+1
                require((d==0)==capped, 'finite ramp optimality iff degree cap')
            if d < F(A,k*(k+1)):
                kept=[E for E,w in zip(edges,y) if w > F(1,k+2)]
                degrees=Counter(v for E in kept for v in E)
                require(all(t <= k+1 for t in degrees.values()), 'ramp retained degree cap')
                removed=m-len(kept)
                budget=(k+1)*(k+2)*(1+F(m,A))*d
                require(removed <= budget, 'ramp exact deletion budget')
                require(b <= F(1,k), 'ramp high-peak exclusion')
                require(b-F(1,k+1) <= d/F(A), 'ramp peak deficit bound')
    return r,m,Y


def field_ops(q):
    require(q in (2,3,4,5), 'fixed finite-field domain')
    if q==4:
        def mul(a,b):
            out=0
            while b:
                if b&1:
                    out^=a
                b>>=1
                a<<=1
                if a&4:
                    a^=7  # F2[x]/(x^2+x+1).
            return out
        return lambda a,b:a^b,mul
    return lambda a,b:(a+b)%q,lambda a,b:(a*b)%q


def affine_design(p,N,details=False):
    add,mul=field_ops(p)
    points=list(product(range(p),repeat=N))
    ids={a:i for i,a in enumerate(points)}
    directions=[]
    for a in points[1:]:
        if next(x for x in a if x) == 1:
            directions.append(a)
    blocks=[]
    parallel=[]
    partof={}
    for part,d in enumerate(directions):
        lines=set()
        for a in points:
            line=frozenset(ids[tuple(add(x,mul(t,z)) for x,z in zip(a,d))] for t in range(p))
            lines.add(line)
        for line in sorted(lines,key=lambda L:sorted(L)):
            if d==(1,)+(0,)*(N-1):
                parallel.append(len(blocks))
            partof[len(blocks)]=part
            blocks.append(line)
    edges=[frozenset(i for i,L in enumerate(blocks) if a in L) for a in range(len(points))]
    r=(p**N-1)//(p-1)
    require(all(len(E)==r for E in edges), 'affine replication')
    require(all(len(L)==p for L in blocks), 'affine block size')
    require(all(len(E&G)==1 for E,G in combinations(edges,2)), 'affine pair design')
    C=frozenset(parallel)
    require(len(C)==p**N//p and all(len(C&E)==1 for E in edges), 'parallel cover')
    base=(edges,[F(1,p)]*len(edges),{i:F(1,r) for i in range(len(blocks))},C)
    return (*base,points,directions,{L:i for i,L in enumerate(blocks)},partof) if details else base


def plateau(p,N,L):
    edges,y,primal,C=affine_design(p,N)
    r=len(edges[0])
    require(len(C)<r, 'cover below rank')
    outside=sorted(set(primal)-C)
    T=C|frozenset(outside[:r-len(C)-1])
    candidates=[T|{v} for v in sorted(set(primal)-T)]
    new=[E for E in candidates if E not in set(edges)][:L]
    require(len(new)==L, 'enough distinct new edges')
    return edges+new,y+[F(0)]*L,primal


def ramp(p,N,padding):
    edges,y,primal,_=affine_design(p,N)
    fresh=max(primal)+1
    padded=[]
    for E in edges:
        added=frozenset(range(fresh,fresh+padding))
        primal.update({v:F(0) for v in added})
        fresh+=padding
        padded.append(E|added)
    return padded,y,primal


def partite_pencil(q,N,L):
    edges,y,primal,C,points,directions,blockids,partof=affine_design(q,N,True)
    add,mul=field_ops(q)
    ids={a:i for i,a in enumerate(points)}
    spaces=set()
    for x,z in combinations(directions,2):
        spaces.add(frozenset(ids[tuple(add(mul(a,u),mul(b,w)) for u,w in zip(x,z))]
                             for a in range(q) for b in range(q)))
    require(all(len(W)==q*q and 0 in W for W in spaces), 'two-dimensional subspaces')
    v=q**N
    require(len(spaces)==(v-1)*(v-q)//((q*q-1)*(q*q-q)), 'Gaussian subspace count')
    new=[]
    for W in sorted(spaces,key=lambda W:sorted(W)):
        z=points[min(W-{0})]
        lines=[]
        for d in directions:
            base=z if ids[d] in W else points[0]
            line=frozenset(ids[tuple(add(a,mul(t,b)) for a,b in zip(base,d))] for t in range(q))
            lines.append(blockids[line])
        E=frozenset(lines)
        require(E not in set(edges) and E not in new, 'distinct partial pencil')
        new.append(E)
    require(len(new)>=L, 'partial pencil supply')
    edges+=new[:L]; y+=[F(0)]*L
    r=len(directions)
    require(all(Counter(partof[v] for v in E)==Counter(range(r)) for E in edges), 'one vertex per part')
    integer_primal={v:F(int(v in C)) for v in primal}
    return edges,y,integer_primal


def partite_ramp(q,N,padding):
    _,_,_,C,_,directions,_,partof=affine_design(q,N,True)
    old_vertex_count=len(partof)
    edges,y,primal=ramp(q,N,padding)
    for v in primal:
        if v>=old_vertex_count:
            partof[v]=len(directions)+(v-old_vertex_count)%padding
    r=len(edges[0])
    require(all(Counter(partof[v] for v in E)==Counter(range(r)) for E in edges), 'padded partite classes')
    return edges,y,{v:F(int(v in C)) for v in primal}


def cloned_class_ramp(q,N,t):
    edges,y,primal,C,_,directions,_,partof=affine_design(q,N,True)
    fresh=max(primal)+1
    padded=[]
    copies={}
    for v in sorted(C):
        copies[v]=frozenset(range(fresh,fresh+t))
        primal.update({w:F(0) for w in copies[v]})
        for j,w in enumerate(sorted(copies[v])):
            partof[w]=len(directions)+j
        fresh+=t
    for E in edges:
        padded.append(E|set().union(*(copies[v] for v in E&C)))
    integer_primal={v:F(int(v in C)) for v in primal}
    require(all(Counter(partof[v] for v in E)==Counter(range(len(directions)+t)) for E in padded),
            'cloned class part partition')
    require(sum(len(E&G)-1 for E,G in combinations(padded,2))==t*len(edges),
            'cloned-class excess formula')
    return padded,y,integer_primal


def main():
    bins=0
    for k in range(2,13):
        for j in range(1,17):
            b=F(1,k+1)+F(j,16)*(F(1,k)-F(1,k+1))
            for ell in range(4*k+1):
                capacity=min(ell*b,1-b)
                for q in range(9):
                    W=capacity*F(q,8)
                    require(W-(1-k*b)*ell <= (k-1)*((k+1)*b-1), 'rational signed-bin grid')
                    bins+=1
    print(f'{bins} exact rational signed-bin diagnostics PASS')
    cases=[('pair plateau',*plateau(2,4,6),2),
           ('triple plateau',*plateau(3,3,8),3),
           ('five-block plateau',*plateau(5,2,4),5),
           ('triple linear ramp',*ramp(3,3,2),2),
           ('five-block linear ramp',*ramp(5,3,1),4),
           ('low-ratio pair ramp',*ramp(2,4,17),None)]
    for name,edges,y,primal,k in cases:
        r,m,Y=check_vector(edges,y,primal)
        if k is None:
            require(Y==F(m,2), 'pair ramp equality')
        else:
            require(Y==finite_bound(r,m,k), 'finite phase equality')
        print(f'{name}: r={r}, m={m}, tau*={Y}, exact optimality and phase equality PASS')
    partite_cases=[('F2 partial pencil',*partite_pencil(2,4,6),2),
                   ('F3 partial pencil',*partite_pencil(3,3,8),3),
                   ('F4 partial pencil',*partite_pencil(4,3,9),4),
                   ('F5 partial pencil',*partite_pencil(5,3,12),5),
                   ('F4 partite ramp',*partite_ramp(4,3,1),3),
                   ('F3 cloned-class ramp',*cloned_class_ramp(3,3,2),2)]
    for name,edges,y,primal,k in partite_cases:
        r,m,Y=check_vector(edges,y,primal)
        require(Y==finite_bound(r,m,k) and all(w in (0,1) for w in primal.values()),
                'partite integer/fractional phase equality')
        print(f'{name}: r={r}, m={m}, tau=tau*={Y}, partite exact phase equality PASS')
    edges,y,primal=partite_pencil(2,5,16)
    r,m,Y=check_vector(edges,y,primal)
    require(Y==finite_bound(r,m,2) and m==3*(r+1)//2, 'finite phase switch certificate')
    new=edges[32:]
    require(len(new)==16 and all(set.intersection(*(set(E) for E in group))
                                for group in combinations(new,4)), 'four-new-edge common vertex')
    print(f'Phase-switch obstruction: r={r}, m={m}, tau*=tau={Y}; degree-3 core deletes at least 13 new edges PASS')
    add,mul=field_ops(4)
    for a,b,c in product(range(4),repeat=3):
        require(add(a,add(b,c))==add(add(a,b),c) and mul(a,mul(b,c))==mul(mul(a,b),c)
                and mul(a,add(b,c))==add(mul(a,b),mul(a,c)), 'F4 exact operations')
    require(all(any(mul(a,b)==1 for b in range(4)) for a in range(1,4)), 'F4 inverses')
    print('F4 field table: exact associativity/distributivity and nonzero inverses PASS')
    ramp_cases=0
    for L in range(13):
        edges,y,primal=plateau(3,3,L)
        for j in range(9):
            scaled=[w*(1-F(j,1000)) for w in y]
            r,m,Y=check_vector(edges,scaled,primal if j==0 else None)
            k=2; A=k*m-(k+1)*((k-1)*r+1)
            d=F(m,k+1)-Y
            if A>0 and d<F(A,k*(k+1)):
                ramp_cases+=1
    print(f'{ramp_cases} strict-ramp deficit/deletion incidence diagnostics PASS')
    # Interior reciprocal-interval peak: its signed bound is attained
    # as an affine expression, while it is not an optimal dual vector.
    edges,y,_,_=affine_design(3,3)
    epsilon=F(1,20)
    y=[y[0]+epsilon]+[z-epsilon/2 for z in y[1:]]
    r,m,Y=check_vector(edges,y)
    b=max(y);g=r+1
    require(Y==m-g+b*(3*g-2*m), 'interior affine identity')
    print(f'Interior nonoptimal peak: r={r}, m={m}, feasible value={Y} PASS')
    # Signed costs cannot be counted repeatedly across intersections.
    shared=[frozenset((0,1,i+2)) for i in range(5)]
    y=[F(2,5)]+[F(3,20)]*4
    check_vector(shared,y)
    b=y[0];B=1-2*b
    exact_score=sum(y)-b-B*4
    repeated_score=sum((y[i]-B)*len(shared[0]&shared[i]) for i in range(1,5))
    require(exact_score==F(-1,5) and repeated_score==F(-2,5),
            'signed-repeat negative control')
    print('Negative signed costs: repeated-intersection conservation error detected PASS')
    fano=[frozenset((i,(i+1)%7,(i+3)%7)) for i in range(7)]
    primal={v:F(1,3) for v in range(7)}
    r,m,Y=check_vector(fano,[F(1,3)]*7,primal)
    require(Y>r*psi(F(m,r)), 'finite correction cannot be dropped')
    require(all(not all(set(C)&E for E in fano) for C in combinations(range(7),2)), 'Fano no two-cover')
    require(all(fano[0]&E for E in fano) and F(3)>finite_bound(r,m,3), 'integer overclaim control')
    print('Fano omitted-correction and fractional-to-integer overclaim controls PASS')
    values={F(3,2):F(1,2),F(7,4):F(7,12),F(5,2):F(2,3),F(11,4):F(11,16)}
    for c,p in values.items():
        require(psi(c)==p, 'sharp curve rational sample')
    print('Four exact frontier values PASS')


if __name__=='__main__':
    main()
