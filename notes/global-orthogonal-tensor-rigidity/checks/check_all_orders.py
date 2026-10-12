"""Exact finite tests of the complete contraction convention and block identity."""
from fractions import Fraction as Q
from itertools import product
from random import Random
from check_linearization import zero, mul, add, comm, require


def contractions(t, m, p):
    return {a: [[t[a+(i,j)] for j in range(m)] for i in range(m)]
            for a in product(range(m), repeat=p-2)}


def residual_squared(xs):
    return sum(v*v for a in xs.values() for b in xs.values()
               for row in comm(a,b) for v in row)


def make_tensor(m, p, rng):
    vals, t = {}, {}
    for inds in product(range(m), repeat=p):
        key=tuple(sorted(inds))
        if key not in vals:
            vals[key]=Q(rng.randint(-3,3),rng.randint(1,4))
        t[inds]=vals[key]
    return t


def rotate(t, m, p):
    # Rational orthogonal reflection, dense for m=2.
    u=[[Q(3,5),Q(4,5)],[Q(4,5),Q(-3,5)]]
    require(m==2,"rotation test dimension")
    out={}
    for inds in product(range(m),repeat=p):
        value=Q(0)
        for js, coeff in t.items():
            weight=coeff
            for i,j in zip(inds,js):
                weight*=u[i][j]
            value+=weight
        out[inds]=value
    return out


def check_case(m,p,rng):
    t=make_tensor(m,p,rng)
    xs=contractions(t,m,p)
    selected={a:x for a,x in xs.items() if 0 not in a}
    bs={a:x[0][1:] for a,x in selected.items()}
    zs={a:[row[1:] for row in x[1:]] for a,x in selected.items()}
    correction_sq=Q(0)
    for a,b in product(selected,repeat=2):
        full=[row[1:] for row in comm(selected[a],selected[b])[1:]]
        corr=[[bs[a][i]*bs[b][j]-bs[b][i]*bs[a][j]
               for j in range(m-1)] for i in range(m-1)]
        require(full==add(comm(zs[a],zs[b]),corr),"higher-order block identity")
        correction_sq+=sum(v*v for row in corr for v in row)
    bsum=sum(v*v for b in bs.values() for v in b)
    mixed=sum(v*v for inds,v in t.items() if 0 in inds and any(i!=0 for i in inds))
    selected_mixed=sum(t[a+(j,0)]**2 for a in xs for j in range(1,m))
    require(mixed<=p*selected_mixed,"aggregate mixed-entry counting bound")
    for k in range(1,p):
        full_k=sum(v*v for inds,v in t.items() if inds.count(0)==k)
        selected_k=sum(t[a+(j,0)]**2 for a in xs for j in range(1,m)
                       if (a+(j,0)).count(0)==k)
        require(p*(p-1)*selected_k==k*(p-k)*full_k,
                "exact mixed permutation fraction")
    require(bsum<=mixed,"mixed-entry subset bound")
    require(correction_sq<=2*bsum*bsum,"correction direct-sum bound")
    if m==2 and p<=5:
        rotated=rotate(t,m,p)
        require(sum(v*v for v in t.values())==sum(v*v for v in rotated.values()),
                "tensor norm rotation invariance")
        require(residual_squared(xs)==residual_squared(contractions(rotated,m,p)),
                "complete residual rotation invariance")
    special={inds:Q(inds.count(1)==1 and all(i in (0,1) for i in inds))
             for inds in product(range(m),repeat=p)}
    sy=contractions(special,m,p)
    a=(0,)*(p-2)
    b=(0,)*(p-3)+(1,)
    require(sy[a][0][:2]==[Q(0),Q(1)] and
            sy[a][1][:2]==[Q(1),Q(0)],"first sharpness contraction")
    require(sy[b][0][:2]==[Q(1),Q(0)] and
            sy[b][1][:2]==[Q(0),Q(0)],"second sharpness contraction")
    require(any(v for row in comm(sy[a],sy[b]) for v in row),
            "sharpness noncommutation")
    if m%2==0:
        harmonic={}
        for inds in product(range(m),repeat=p):
            same_block=len({i//2 for i in inds})==1
            ell=sum(i%2 for i in inds)
            harmonic[inds]=Q((1,0,-1,0)[ell%4] if same_block else 0)
        require(sum(v*v for v in harmonic.values())==(m//2)*2**(p-1),
                "harmonic direct-sum norm")
        require(residual_squared(contractions(harmonic,m,p))==
                (m//2)*2**(2*p-2),"harmonic direct-sum residual")


def main():
    rng=Random(20261007)
    for m,p in ((2,3),(2,4),(2,5),(2,6),(2,7),(3,3),(3,4),(3,5),(4,3)):
        check_case(m,p,rng)
        print(f"m={m}, order={p}: block, aggregate counting, indexing, sharpness checks PASS")
    print("ALL EXACT ALL-ORDERS CHECKS PASSED")


if __name__=="__main__":
    main()
