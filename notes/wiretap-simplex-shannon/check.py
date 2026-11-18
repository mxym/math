"""Finite exact checks only, not a proof. No third-party dependencies."""
from itertools import combinations_with_replacement, product
from math import comb

def require(a, label):
    if not a:
        raise RuntimeError(label)

def directions(q, d):
    return [v for v in product(range(q), repeat=d)
            if next((c for c in v if c), 0) == 1]

def rank(vectors, q):
    pivots = {}
    for raw in vectors:
        v = list(raw)
        for i in range(len(v)):
            if v[i] == 0:
                continue
            if i in pivots:
                c = v[i]
                v = [(a-c*b)%q for a,b in zip(v, pivots[i])]
            else:
                c = pow(v[i], -1, q)
                pivots[i] = tuple(a*c%q for a in v)
                break
    return len(pivots)

def rtable(vs, q):
    return [rank((v for j,v in enumerate(vs) if (s>>j)&1),q)
            for s in range(1<<len(vs))]

def physical(hist, r, n):
    cols = [0]*hist[0] + [1<<i for i,b in enumerate(hist[1:]) for _ in range(b)]
    masks = [0]*(1<<n)
    for s in range(1,1<<n):
        l = s & -s
        masks[s] = masks[s-l] | cols[l.bit_length()-1]
    coeff = [0]*(n+1)
    for s,b in enumerate(masks):
        coeff[s.bit_count()] += r[b]
    return coeff

def aggregate(hist, table, a,b):
    # Exact expected rank, times b**n, for erasure a/b.
    weights=[1]
    for m in hist[1:]:
        off = a**m
        on = b**m-off
        weights = [p*off for p in weights] + [p*on for p in weights]
    return (b**hist[0])*sum(p*r for p,r in zip(weights,table))

def exact_num(coeff,a,b,n):
    return sum(c*(b-a)**j * a**(n-j) for j,c in enumerate(coeff))

def enum(q,d,t):
    vs = directions(q,d)
    L=len(vs); n=t*L
    require(L==(q**d-1)//(q-1),'projective count')
    R=rtable(vs,q)
    best=(0,)+(t,)*L
    B=physical(best,R,n)
    total=full=tests=0
    for s in combinations_with_replacement(range(L+1),n):
        h=tuple(s.count(i) for i in range(L+1))
        total+=1
        mask=sum(1<<i for i,m in enumerate(h[1:]) if m)
        if R[mask]!=d:
            continue
        full+=1; C=physical(h,R,n)
        for a,b in [(0,1),(1,5),(1,2),(2,3),(4,5),(1,1)]:
            v=exact_num(C,a,b,n)
            require(v==aggregate(h,R,a,b),('law',q,d,t,h,a,b))
            delta=exact_num(B,a,b,n)-v
            require(delta>=0 and (delta==0)==(a in (0,b) or h==best),
                    ('uniqueness',q,d,t,h,a,b,delta))
            tests+=1
    require(total==comb(n+L,L) and full and tests==6*full,'coverage')
    print(f'q={q},d={d},t={t}: {total} histograms, {full} spanning, {tests} rate checks')
    return total,full,tests

def dot(a,b,q):
    return sum(x*y for x,y in zip(a,b))%q

def fiber_and_dual(q,cols):
    # Enumerate actual codewords and posterior message counts, not an entropy formula.
    n=len(cols); d=len(cols[0])
    G=list(zip(*cols)); R=rtable(cols,q)
    vs=list(product(range(q),repeat=n))
    primal={tuple(dot(v,c,q) for c in cols)
            for v in product(range(q),repeat=d)}
    dual=[v for v in vs if all(dot(v,g,q)==0 for g in G)]
    require(len(primal)==q**d and len(dual)==q**(n-d),'dimension')
    labels={}
    for v in vs:
        if v in labels: continue
        for w in primal:
            x=tuple((a+b)%q for a,b in zip(v,w))
            require(x not in labels,'coset repeated')
            labels[x]=v
    require(len(labels)==q**n,'labels')
    rows=0
    for s in range(1<<n):
        idx=[i for i in range(n) if (s>>i)&1]
        fibers={}
        for v in vs:
            y=tuple(v[i] for i in idx)
            counts=fibers.setdefault(y,{})
            m=labels[v]; counts[m]=counts.get(m,0)+1
        require(len(fibers)==q**len(idx),'observation count')
        for counts in fibers.values():
            require(len(counts)==q**(n-d-len(idx)+R[s]) and
                    set(counts.values())=={q**(d-R[s])},'posterior')
            rows+=1
        dual_projections={tuple(v[i] for i in idx) for v in dual}
        exp=len(idx)-d+R[(1<<n)-1-s]
        require(exp>=0 and len(dual_projections)==q**exp,'dual rank')
    require(rows==(q+1)**n,'posterior count')
    return 1<<n,rows

def hessian(q,d):
    vs=directions(q,d); k=len(vs); R=rtable(vs,q); count=0
    for s,rs in enumerate(R):
        # Quotient classes characterized by the set of directions
        # newly spanned after adjoining the point.
        low={e for e in range(k) if R[s|(1<<e)]==rs}
        cls={}
        for e in range(k):
            if e not in low:
                a=s|(1<<e)
                cls[e]=frozenset(j for j in range(k) if j not in low and R[a|(1<<j)]==R[a])
        for i in range(k):
            for j in range(k):
                got=R[s|(1<<i)]+R[s|(1<<j)]-rs-R[s|(1<<i)|(1<<j)]
                want=int(i in cls and j in cls and cls[i]==cls[j])
                require(got==want and (s!=0 or got==int(i==j)),'negative Hessian')
                count+=1
    return count

if __name__=='__main__':
    cases=(enum(2,2,1),enum(2,2,2),enum(2,3,1),enum(3,2,1))
    examples=((2,[(1,0),(1,0),(0,1),(0,0)]),(2,directions(2,3)),
              (3,directions(3,2)),(3,[(0,0),(2,0),(1,0),(1,1)]))
    fibers=[fiber_and_dual(*args) for args in examples]
    H=hessian(2,3)+hessian(3,2)
    require(len(cases)==4 and len(fibers)==4 and H==128*49+16*16,'overall coverage')
    print(f'{sum(v[0] for v in fibers)} subset/duality checks, {sum(v[1] for v in fibers)} posterior fibers, {H} Hessian entries')
    print('PASS: all exact checks completed')
