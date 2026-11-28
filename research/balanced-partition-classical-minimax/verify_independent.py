#!/usr/bin/env python3
"""Independent weighted-subset and conditional guessing frontier checks."""
from fractions import Fraction as F
from itertools import combinations, product
from functools import lru_cache


@lru_cache(None)
def partitions(n,d,lo=0):
    if d==1:
        return ((n,),) if n>=lo else ()
    return tuple((a,)+b for a in range(lo,n//d+1) for b in partitions(n-a,d-1,a))


def loss(a,weights,D):
    return abs(sum(weights[i] for i in a)-F(sum(weights),D))


def test_weighted():
    checks,comps=0,0
    for N in range(1,6):
        W=tuple(w for w in product(range(3), repeat=N) if sum(w)>0 and tuple(sorted(w))==w)
        for D,w in product(range(1,6), W):
            g = []
            for k in range(N+1):
                subsets=tuple(combinations(range(N),k))
                g.append(sum(loss(a,w,D) for a in subsets)/len(subsets))
            assert all(g[k]+g[k+2]>=2*g[k+1] for k in range(N-1))
            q,r = divmod(N,D)
            target = (D-r)*g[q]+(r*g[q+1] if r else 0)
            for sizes in partitions(N,D):
                assert target<=sum(g[a] for a in sizes)
                comps+=1
            checks+=1
    return checks,comps


def enumerate_flat(N,k,D):
    # A single fixed balanced coloring and all source supports, no HG formula.
    colors = tuple(i%D for i in range(N))
    errors = []
    for a in combinations(range(N),k):
        c=tuple(colors[i] for i in a)
        errors.append(F(sum(abs(c.count(j)*D-k) for j in range(D)),2*k*D))
    return sum(errors)/len(errors)


def hull(points):
    # Upper concave chain; throw away internal vertices with a nondecreasing slope.
    chain=[]
    for x,y in points:
        while len(chain)>=2:
            a,b=chain[-2:]
            if (b[1]-a[1])*(x-b[0])>(y-b[1])*(b[0]-a[0]):
                break
            chain.pop()
        chain.append((x,y))
    return chain


def hull_at(chain,g):
    val=max(y for x,y in chain if x<=g)
    for (x,y),(z,w) in zip(chain,chain[1:]):
        if x<=g<=z:
            val=max(val,y+(w-y)*(g-x)/(z-x))
    return val


def test_frontier():
    check,layer=0,0
    for N,D in product(range(1,9),range(1,7)):
        vals=[enumerate_flat(N,k,D) for k in range(1,N+1)]
        points=[(F(1,j),vals[j-1]) for j in range(N,0,-1)]
        cap=hull(points)
        budgets=sorted({F(1,N),F(1)} | {F(i,36) for i in range(37) if F(i,36)>=F(1,N)})
        for g in budgets:
            # Vary probabilities on every two-type mixture, with optimum at an endpoint.
            candidates=[y for x,y in points if x<=g]
            for (x,y),(z,w) in combinations(points,2):
                if x<=g<z:
                    lam=(z-g)/(z-x)
                    candidates.append(lam*y+(1-lam)*w)
            assert hull_at(cap,g)==max(candidates)
            check+=1
        if N<=5:
            for w in product(range(3),repeat=N):
                if not sum(w):
                    continue
                p=sorted((F(c,sum(w)) for c in w),reverse=True)+[F(0)]
                weights=[j*(p[j-1]-p[j]) for j in range(1,N+1)]
                assert tuple(sum(weights[j-1]/j for j in range(i,N+1)) for i in range(1,N+1))==tuple(p[:-1])
                assert sum(weights)==1
                assert sum(wt/j for j,wt in enumerate(weights,1))==p[0]
                assert sum(wt*v for wt,v in zip(weights,vals))<=hull_at(cap,p[0])
                layer+=1
    pts=[(F(1,j),enumerate_flat(4,j,2)) for j in range(4,0,-1)]
    assert hull_at(hull(pts),F(1,2))==F(1,4)
    assert enumerate_flat(4,2,2)==F(1,6)
    return check,layer


def test_partial_conditioning():
    # Fixed finite rational laws with overlapping conditional supports.
    # Compare the actual balanced strong law to the refined side information law.
    tests=0
    for N,D in product(range(2,7),range(1,6)):
        bins=tuple(tuple(x for x in range(N) if x%D==j) for j in range(D))
        shapes=tuple(sorted({tuple(F(w,sum(ws)) for w in ws)
                            for ws in product(range(3),repeat=N) if sum(ws) and tuple(sorted(ws))==ws}))
        flat=[enumerate_flat(N,j,D) for j in range(1,N+1)]
        chain=hull([(F(1,j),flat[j-1]) for j in range(N,0,-1)])
        actual=[]
        refined=[]
        for shape in shapes:
            loss=F(0)
            for b in bins:
                subsets=tuple(combinations(shape,len(b)))
                loss+=sum(abs(sum(a)-F(1,D)) for a in subsets)/len(subsets)
            actual.append(loss/2)
            probs=shape[::-1]+(F(0),)
            refined.append(sum(j*(probs[j-1]-probs[j])*flat[j-1] for j in range(1,N+1)))
        for i,j in product(range(len(shapes)),repeat=2):
            g=(shapes[i][-1]+2*shapes[j][-1])/3
            a=(actual[i]+2*actual[j])/3
            b=(refined[i]+2*refined[j])/3
            assert a<=b<=hull_at(chain,g)
            tests+=1
    return tests


if __name__ == "__main__":
    a,b=test_weighted()
    print(f"Weighted balance: {a} exact subset curves, {b} size partitions")
    c,d=test_frontier()
    print(f"Classical guessing hull: {c} budgets, {d} layer refinements, strict side-information example PASS")
    print(f"Conditional refinement: {test_partial_conditioning()} two-label laws")
