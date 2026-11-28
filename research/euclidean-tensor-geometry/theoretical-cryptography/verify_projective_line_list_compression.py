#!/usr/bin/env python3
"""Exact finite examples for list-dependent line compression; no external input."""
from collections import Counter, defaultdict
from itertools import combinations, product
from random import Random


def dot(x, y):
    return sum(a*b for a, b in zip(x,y))


def rref(rows, d, p):
    a = [[v % p for v in x] for x in rows]
    r = 0
    for j in range(d):
        s = next((i for i in range(r,len(a)) if a[i][j]), None)
        if s is None:
            continue
        a[r],a[s] = a[s],a[r]
        t = pow(a[r][j],-1,p)
        a[r] = [x*t % p for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][j]:
                t = a[i][j]
                a[i] = [(x-t*y) % p for x,y in zip(a[i],a[r])]
        r += 1
    return tuple(map(tuple,a[:r]))


def perp(a, d, p):
    piv = [next(j for j,t in enumerate(x) if t) for x in a]
    out = []
    for j in range(d):
        if j not in piv:
            x = [0]*d
            x[j] = 1
            for i,z in enumerate(piv):
                x[z] = (-a[i][j]) % p
            out.append(x)
    return rref(out,d,p)


def meet(u,v,d,p):
    return perp(rref(perp(u,d,p)+perp(v,d,p),d,p),d,p)


def count(dim,p):
    return (p**dim-1)//(p-1)


def point(x,p):
    v = next((a for a in x if a),0)
    return tuple(a*pow(v,-1,p) % p for a in x) if v else ()


def direct_lines(u,d,p):
    return {point(tuple(sum(a*v[j] for a,v in zip(z,u)) % p
                       for j in range(d)),p)
            for z in product(range(p),repeat=len(u))} - {()}


def obj(lc,p):
    return sum(c*count(len(u),p) for u,c in lc)


def lattice(us,d,p):
    cl = {u for u in us if u}
    first = tuple(cl)
    old = set()
    while cl != old:
        old = set(cl)
        for u in old:
            for v in first:
                w = meet(u,v,d,p)
                if w:
                    cl.add(w)
    c = {}
    for u in sorted(cl,key=lambda u:(-len(u),u)):
        c[u] = 1-sum(b for v,b in c.items() if len(v)>len(u)
                     and len(rref(u+v,d,p))==len(v))
    return list(c.items())


trace = Counter()


def compress(us,d,p,distinct):
    lc = lattice(us,d,p) if distinct else [(u,1) for u in us]
    original_lc = lc
    robust = p <= 5 and d <= 6
    initial = H = obj(lc,p)
    if robust:
        uu = [direct_lines(u,d,p) for u in us]
        assert H == (len(set().union(*uu)) if distinct else sum(map(len,uu)))
    out = []
    pre = [tuple(tuple(int(a==b) for a in range(d)) for b in range(j))
           for j in range(d+1)]
    while H:
        row = []
        line_sets = [(direct_lines(u,d,p),c) for u,c in lc] if robust else []
        for j in range(d):
            weights = defaultdict(int)
            for u,c in lc:
                v = meet(u,pre[j+1],d,p)
                w = next((x for x in v if x[j]),None)
                if w is not None:
                    t = -dot(w,row)*pow(w[j],-1,p) % p
                    if all((dot(x,row)+t*x[j]) % p == 0 for x in v):
                        weights[t] += c*p**(len(v)-1)
            missing = 0
            for a in sorted(weights):
                if a != missing:
                    break
                missing += 1
            if missing < p:
                weights[missing] = 0
            t = min(weights,key=lambda z:(weights[z],z))
            if robust:
                vals=[]
                for x in range(p):
                    rr=row+[x]
                    vals.append(sum(c*sum(int(not any(y[j+1:]))
                                      *int(dot(y,rr) % p == 0)
                                      for y in lines) for lines,c in line_sets))
                assert vals[t] == min(vals)
                trace["prefix choices"] += 1
            row.append(t)
        K = perp(rref([row],d,p),d,p)
        lc = [(meet(u,K,d,p),c) for u,c in lc]
        new = obj(lc,p)
        assert 0 <= p*new <= H
        out.append(tuple(row))
        H = new
    assert len(out) <= d and len(rref(out,d,p)) == len(out)
    assert initial==0 or p**(len(out)-1) <= initial
    for u in us:
        assert len(rref((apply(out,x,p) for x in u),len(out),p)) == len(u)
    if robust and distinct:
        assert all(sum(c for u,c in original_lc
                       if len(rref(u+(x,),d,p))==len(u)) == 1
                   for x in set().union(*uu))
    trace["families"] += 1
    return out, initial


def apply(A,x,p):
    return tuple(dot(a,x) % p for a in A)


def planes(lines,extra,d,p):
    ds=sorted({point(x,p) for x in lines}-{()})
    return [(x,) for x in ds]+[rref([x,y],d,p) for x,y in combinations(ds,2)]+(
         [(point(extra,p),)] if any(extra) else [])


def forward(start,items,p):
    z = Counter({start:1})
    den = 1
    for v,L in items:
        w = Counter()
        for x,n in z.items():
            for t in range(min(p,L)):
                y = tuple((a+t*b) % p for a,b in zip(x,v))
                w[y] += n * (L//p + int(t<L%p))
        z=w
        den*=L
    assert sum(z.values()) == den
    return z,den


def same(a,b):
    x,d=a; y,e=b
    return all(x[t]*e==y[t]*d for t in x.keys() | y.keys())


def quotient_law(A,law,p):
    start,data=law
    return apply(A,start,p),[(apply(A,x,p),L) for x,L in data]


def check_laws(a,b,d,p):
    wa,wb=[rref([x for x,L in data if L%p==0],d,p) for _,data in (a,b)]
    if wa!=wb:
        r=[x for u,v in ((wa,wb),(wb,wa)) for x in perp(u,d,p)
           if any(dot(x,y) % p for y in v)]
        assert r
        T=[r[0]]
    else:
        Q=perp(wa,d,p)
        aa,bb=[quotient_law(Q,t,p) for t in (a,b)]
        aa,bb=[(z,[(x,L) for x,L in dat if any(x)]) for z,dat in (aa,bb)]
        D=len(Q)
        def center(t):
            z,items=t
            if p==2:
                return z
            return tuple((a+pow(2,-1,p)*sum((L-1)*v[i] for v,L in items)) % p
                         for i,a in enumerate(z))
        e=tuple((x-y) % p for x,y in zip(center(aa),center(bb)))
        ls=planes([v for _,da in (aa,bb) for v,_ in da],e,D,p)
        A,_=compress(ls,D,p,True)
        T=[tuple(sum(v[i]*q[j] for i,q in enumerate(Q)) % p
                 for j in range(d)) for v in A]
    original=same(forward(*a,p),forward(*b,p))
    image=same(forward(*quotient_law(T,a,p),p),
               forward(*quotient_law(T,b,p),p))
    assert original == image
    trace["equal laws" if original else "unequal laws"]+=1


rng=Random(567439)
for p in (2,3,5):
    for d in (2,3,4):
        coords=list(product(range(p),repeat=d))
        for trial in range(42):
            us=[rref(rng.choices(coords,k=rng.randrange(min(3,d)+1)),d,p)
                for _ in range(rng.randrange(8))]
            C1,H1=compress(us,d,p,False)
            C2,H2=compress(us,d,p,True)
            assert H2<=H1
        for trial in range(55):
            a=(rng.choice(coords),[(rng.choice(coords),rng.randrange(1,2*p+4))
                                   for _ in range(rng.randrange(6))])
            if trial%3==0: # Reverse all arithmetic progressions exactly.
                b=(tuple((a[0][j]+sum((L-1)*x[j] for x,L in a[1])) % p
                         for j in range(d)),
                   [(tuple((-t) % p for t in x),L) for x,L in reversed(a[1])])
            else:
                b=(rng.choice(coords),[(rng.choice(coords),rng.randrange(1,2*p+4))
                                       for _ in range(rng.randrange(6))])
            check_laws(a,b,d,p)

p=1_000_000_007
for idx in range(4):
    d=9
    directions=[tuple(rng.randrange(p) for _ in range(d)) for _ in range(6)]
    ws=planes(directions,(0,)*d,d,p)
    A,H=compress(ws,d,p,False)
    B,J=compress(ws,d,p,True)
    assert len(A)==len(B)==2 and J <= H
p,d=3,4
ls=[x for x in product(range(p),repeat=d) if x==point(x,p)
    and (not any(x[:2]) or not any(x[2:]))]
A,H=compress(planes(ls,(0,)*d,d,p),d,p,True)
assert len(A)==4 and H==40
p,d=2,6
ls=[x+(0,)*3 for x in product(range(2),repeat=3) if any(x)]
ws=planes(ls,(0,)*d,d,p)
A,H=compress(ws,d,p,False)
B,J=compress(ws,d,p,True)
assert (len(B),J,H)==(3,7,70)
assert 2**3<=H and H<2**7
print("PASS exact projective-line compression:", dict(trace))
