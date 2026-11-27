#!/usr/bin/env python3
"""Independent finite tests on integer slabs, matchings, restrictions."""
from itertools import product, groupby, combinations


def count_relevant(T,n):
    return sum(any(((T>>x)^(T>>(x^(1<<j))))&1 for x in range(1<<n))
               for j in range(n))


errs=((0,1),(1,4),(1,3),(1,2),(3,5))
Ls=[1+2*a//(b-a) for a,b in errs]
pairs = 0
slab_families=0
for n in range(1,5):
    N=1<<n
    allmask=(1<<N)-1
    sets=[set() for _ in errs]
    for A in product((-2,-1,0,1,2),repeat=n):
        subset_sum=[sum(A[j] for j in range(n) if (x>>j)&1) for x in range(N)]
        for C in range(-4,5):
            vals=[abs(C+t) for t in subset_sum]
            for scale in (1,2,3):
                big=[u >= scale for u in vals]
                if all(big) or not any(big):
                    continue
                small=max(u for u in vals if u < scale)
                f=sum(1<<j for j,b in enumerate(big) if b)
                for e,(a,b) in enumerate(errs):
                    if b*small <= a*scale:
                        sets[e].add(f)
    slab_families += sum(map(len,sets))
    maxima=[[0]*len(errs) for _ in errs]
    for i,fs in enumerate(sets):
        for j,gs in enumerate(sets):
            for f in fs:
                if allmask ^ f in gs:
                    m=count_relevant(f,n)
                    assert m<=Ls[i]+Ls[j]
                    maxima[i][j]=max(maxima[i][j],m)
                    pairs+=1
    assert maxima[0][0]==min(n,2)
    print(f"bounded affine sweep n={n}: label sets {[len(F) for F in sets]}, maxima by diagonal errors {[maxima[i][i] for i in range(len(errs))]}")
print(f"bounded affine sweep: {slab_families} error-labelled supports, {pairs} feasible complementary pairs")

def matchings(xs,n):
    if not n:
        yield ()
    elif len(xs)>=2*n:
        i=xs[0]
        yield from matchings(xs[1:],n)
        for j in xs[1:]:
            for M in matchings(tuple(k for k in xs[1:] if k!=j),n-1):
                yield ((i,j),)+M

tensor_pairs=0
covered=0
for d in range(1,4):
    for L in range(1,5):
        m=2*d+L-1
        target={x for x in range(1<<m) if d<=x.bit_count()<=d+L-1}
        union=set()
        for mat in matchings(tuple(range(m)),d):
            M={x for x in range(1<<m)
               if all(((x>>i)^(x>>j))&1 for i,j in mat)}
            assert M<=target
            union.update(M)
            tensor_pairs+=1
        assert union==target
        covered+=len(target)
print(f"mixed exact slabs: 12 instances, {tensor_pairs} matching products span supports covering {covered} slab points")

preds=runs=weights=0
for n in range(1,11):
    for table in product((0,1),repeat=n+1):
        if min(table)==max(table):
            continue
        lo=0
        for b,g in groupby(table):
            length=len(list(g))
            hi=lo+length-1
            # Directly enumerate every allowed free weight, using the indicated
            # fixing pattern. For the first run the fresh bits are negated.
            fixed_ones = lo-1 if lo else 0
            real=[table[fixed_ones+(j if lo else length-j)] for j in range(length+1)]
            assert real==[1-b]+[b]*length
            assert fixed_ones+length<=n
            lo=hi+1
            runs+=1
            weights+=len(real)
        assert lo==n+1
        preds+=1
print(f"symmetric projections: {preds} nonconstant predicates, {runs} runs, {weights} projected layer values")

# This example has degree-one witnesses but is not linearly thresholdable:
# across both diagonals of the two-cube lies different XOR label.
p=[x-y for x,y in product((0,1),repeat=2)]
q=[x+y-1 for x,y in product((0,1),repeat=2)]
f=[int(bool(v)) for v in p]
assert [int(bool(v)) for v in q]==[1-b for b in f]
assert f==[0,1,1,0] and sum((-1)**i*f[x] for x,i in enumerate((0,1,1,2)))==-2
print("literal constant-one negative control: XOR2, degree-one pair but nonzero top approximation obstruction")
