"""Independent CRT-product evaluation and exact field interpolation."""

from functools import reduce
from itertools import combinations, product
from random import Random
from sympy import QQ, CRootOf, Symbol

P = 3578681
A = 153
B = A*A-19
Z = (0,0,0)
ONE = (1,1,0)
THETA = (A,0,1)


def mul(a,b):
    # CRT coordinates: evaluation at the root A, then coefficients in
    # F_P[x]/(x^2+A*x+B).  This is not a power-basis cubic reduction.
    u,v,w = a
    x,y,z = b
    return (u*x % P, (v*y-B*w*z) % P, (v*z+w*y-A*w*z) % P)


def add(a,b):
    return tuple((x+y)%P for x,y in zip(a,b))


def sub(a,b):
    return tuple((x-y)%P for x,y in zip(a,b))


def scale(v,c):
    return tuple(c*x%P for x in v)


def vs(w,z):
    return tuple(sub(a,b) for a,b in zip(w,z))


def inv(w):
    u,v,b = w
    q = (v*(v-A*b)+B*b*b) % P
    assert u and q
    j = pow(q,-1,P)
    out=(pow(u,-1,P),(v-A*b)*j%P,-b*j%P)
    assert mul(out,w)==ONE
    return out


def vandermonde_test(xs):
    count = 0
    for h in range(2,7):
        for I in combinations(range(6),h):
            v = reduce(mul,(sub(xs[j],xs[i]) for i,j in combinations(I,2)),ONE)
            assert mul(v,inv(v))==ONE
            count+=1
    return count


def project_extra(w, xs, t, all_indices):
    anchor_x = [xs[i] for i in all_indices[:t+1]]
    count=0
    for j,k in enumerate(all_indices[t+1:],t+1):
        coeff=[]
        for u,xi in enumerate(anchor_x):
            numer=reduce(mul,(sub(xs[k],xr) for v,xr in enumerate(anchor_x) if v!=u),ONE)
            denom=reduce(mul,(sub(xi,xr) for v,xr in enumerate(anchor_x) if v!=u),ONE)
            coeff.append(mul(numer,inv(denom)))
        for dim in range(2):
            pred=reduce(add,(mul(a,c[dim]) for a,c in zip(coeff,w)),Z)
            assert pred==w[j][dim]
        count+=1
    return count


def mat_word(basis, actions, xs):
    out=[]
    for x in xs:
        powers=[ONE]
        for _ in basis:
            powers.append(mul(powers[-1],x))
        vals=(Z,Z)
        for r,v in enumerate(basis,1):
            e = actions[v[0]]
            h = actions[v[1]]
            row=tuple(scale(powers[r],e[i]+h[i]) for i in range(2))
            vals=tuple(add(u,z) for u,z in zip(vals,row))
        out.append(vals)
    return tuple(out)


def graph_checks():
    # The two ring factors are comaximal. Their product is a cubic
    # ring of size P^3, and multiplication in the two CRT coordinates
    # shows explicitly why the alphabet ring is not a field.
    assert (A*A+A*A+B)%P!=0
    assert mul((1,0,0),(0,1,0))==Z
    th2=mul(THETA,THETA)
    xs=(Z,th2,ONE,scale(ONE,-1),add(ONE,th2),scale(ONE,2))
    unit = ((1,0),(-1,0),(0,1),(0,-1))
    p0=(1,0)
    p1=(0,1)
    def neg(v):
        return tuple(-x for x in v)
    count=extra=0
    vandermonde_count=vandermonde_test(xs)
    for t in (2,3,4):
        C=set()
        for e in unit:
            for h in unit:
                if sum(x*y for x,y in zip(e,h)):
                    continue
                action={p0:e,neg(p0):neg(e),p1:h,neg(p1):neg(h)}
                pat=(((1,0),(0,0)),((0,1),(0,0)),((-1,0),(0,0)),((0,-1),(0,0)))[:t]
                action[(0,0)]=(0,0)
                C.add(mat_word(pat,action,xs))
        assert len(C)==8
        for k in range(t+1,7):
            for I in combinations(range(6),k):
                r=I[0]
                # Build actual rooted projection sets from entire words
                # (and their translations) rather than constructing secants.
                normalized = {tuple(vs(w[j],w[r]) for j in I) for w in C}
                allowed={pair:{vs(w[pair[1]],w[pair[0]]) for w in C}
                         for pair in combinations(I,2)}
                domains=[{w[pos] for w in normalized} for pos in range(k)]
                all_ok=set()
                for w in product(*domains):
                    if all(vs(w[v],w[u]) in allowed[I[u],I[v]]
                           for u,v in combinations(range(k),2)):
                        all_ok.add(w)
                assert all_ok==normalized and len(all_ok)==8
                count+=len(all_ok)
                extra+=sum(project_extra(w,xs,t,I) for w in all_ok)
    print(f"Independent CRT-product encoding: {count} rooted tuples, "
          f"{extra} extra-point reconstructions, {vandermonde_count} unit Vandermondes")


def interpolate(xs, ys, K):
    q=[K.zero]*len(xs)
    for i,(x,y) in enumerate(zip(xs,ys)):
        term=[K.one]
        den=K.one
        for j,z in enumerate(xs):
            if i==j:
                continue
            out=[K.zero]*(len(term)+1)
            for k,c in enumerate(term):
                out[k]-=c*z
                out[k+1]+=c
            term=out
            den*=x-z
        for j,c in enumerate(term):
            q[j]+=y*c/den
    return q


def is_R(a):
    return all(c.denominator==1 for c in a.to_list())


def local_crt(xs, ys, K, p):
    def key(x):
        out=[a.numerator % p for a in x.to_list()]
        return tuple([0]*(3-len(out))+out)
    def local_coeffs(f):
        return all(a.denominator%p for c in f.coeffs() for a in c.to_list())
    ring=K.poly_ring("Y")
    Y=ring.gens[0]
    groups={}
    for i,x in enumerate(xs):
        groups.setdefault(key(x),[]).append(i)
    J=[(tuple(subset),reduce(lambda a,b:a*b,(Y-xs[i] for i in subset),Y**0))
       for subset in groups.values()]
    M=reduce(lambda a,b:a*b,(f for _,f in J),Y**0)
    out=ring.zero
    paired=0
    for idx,f in J:
        assert 1<=len(idx)<=2
        i=idx[0]
        line=Y**0 * ys[i]
        if len(idx)==2:
            j=idx[1]
            line+=(Y-xs[i]) * ((ys[j]-ys[i])/(xs[j]-xs[i]))
            paired+=1
        other,r=M.div(f)
        assert not r
        u,_,g=other.gcdex(f)
        assert g==Y**0
        assert local_coeffs(u) and local_coeffs(line)
        out+=line*other*u
    rem=out.rem(M)
    assert rem.degree()<len(xs)
    assert local_coeffs(rem)
    return [rem.get((i,),K.zero) for i in range(len(xs))], paired


def interpolation_checks():
    x=Symbol("x")
    K=QQ.algebraic_field(CRootOf(x**3-19*x+11,0))
    z=K.unit
    nodes=(K.zero,z**2,K.one,-K.one,K.one+z**2,K.one+K.one)
    rng=Random(96372)
    checked=paired=0
    for h in range(2,7):
        for I in combinations(range(6),h):
            xs=[nodes[i] for i in I]
            q=[sum((K.convert(rng.randrange(-2,3))*z**k for k in range(3)),K.zero)
               for _ in range(h)]
            ys=[sum((c*x**i for i,c in enumerate(q)),K.zero) for x in xs]
            assert all(is_R((ys[j]-ys[i])/(xs[j]-xs[i])) for i,j in combinations(range(h),2))
            assert q==interpolate(xs,ys,K)
            actual,pairs=local_crt(xs,ys,K,2)
            assert actual==q
            paired+=pairs
            checked+=1
    # When all three evaluation points coincide mod 2, pair divisibility
    # alone is insufficient: interpolate (0,0,4) on (0,2,4).
    xs=[K.convert(i) for i in (0,2,4)]
    ys=[K.convert(i) for i in (0,0,4)]
    assert all(is_R((ys[j]-ys[i])/(xs[j]-xs[i])) for i,j in combinations(range(3),2))
    assert interpolate(xs,ys,K)==[K.zero,-K.one,K.one/K.convert(2)]
    assert not is_R(K.one/K.convert(2))
    assert paired==32
    print(f"Independent exact interpolation: {checked} sets by direct Lagrange and "
          f"local CRT at (2), {paired} paired residue classes; nonseparated negative control rejected")


if __name__ == "__main__":
    graph_checks()
    interpolation_checks()
