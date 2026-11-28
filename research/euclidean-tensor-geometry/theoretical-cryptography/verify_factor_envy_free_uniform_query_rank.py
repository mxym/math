"""Examples and exact algebra checks for the envy-free transcript rank lemma."""
from fractions import Fraction as F
from random import Random

if not __debug__:
    raise RuntimeError("Run without -O")

def interval(n,a,b):
    return [int(a <= j < b) for j in range(n)]

def rref(W,n):
    M=[list(map(F,r)) for r in W]
    I=[]
    for j in range(n):
        h=next((r for r in range(len(I),len(M)) if M[r][j]), None)
        if h is None:
            continue
        k=len(I)
        M[k],M[h]=M[h],M[k]
        pivot=M[k][j]
        M[k]=[x/pivot for x in M[k]]
        for r in range(len(M)):
            if r!=k and M[r][j]:
                M[r]=[x-M[r][j]*y for x,y in zip(M[r],M[k])]
        I.append(j)
    return M,I

def dot(v,w): return sum(x*y for x,y in zip(v,w))

def test(n,queries,c):
    Z=[(0,n)]+queries
    W=[interval(n,a,b) for a,b in Z]
    R,I=rref(W,n)
    in_span=len(rref(W+[c],n)[1])==len(I)
    root=list(range(n+1))
    def find(i):
        while root[i]!=i:
            i=root[i]
        return i
    for a,b in Z:
        root[find(a)]=find(b)
    comp={find(i):0 for i in range(n+1)}
    ext=[0]+c+[0]
    for j in range(n+1):
        comp[find(j)]+=ext[j+1]-ext[j]
    assert len(I)==n+1-len(comp)
    assert in_span==all(not x for x in comp.values())
    if not in_span:
        for k in range(n):
            if k in I:
                continue
            v=[F(0)]*n
            v[k]=F(1)
            for r,pivot in enumerate(I):
                v[pivot]=-R[r][k]
            y=dot(c,v)
            if y==0:
                continue
            # Uniform length 1/n cells. Keep every perturbed density
            # within [3/4,5/4] while making the comparison positive.
            scale=F(1,4*n)/max(map(abs,v))
            v=[(scale if y>0 else -scale)*z for z in v]
            assert not any(dot(v,r) for r in W)
            assert dot(v,c)>0
            assert all(F(3,4)<=1+n*z<=F(5,4) for z in v)
            return False
        raise AssertionError("missing rational separating witness")
    return True

# Touching every boundary does not imply identifying all contrasts.
assert not test(4,[(0,2),(1,3)],[-1,1,0,0])
for j in range(1,4):
    assert test(4,[(0,k) for k in range(1,4)],
                [int(i==j)-int(i==0) for i in range(4)])

# Exact check with arbitrary disjoint piece labels and interval endpoints.
rng=Random(20261128)
counts={True:0,False:0}
for _ in range(240):
    n=rng.randint(4,18)
    m=rng.randint(2,4)
    labels=list(range(m))+[rng.randrange(m) for _ in range(n-m)]
    rng.shuffle(labels)
    a,b=rng.sample(range(m),2)
    c=[int(j==a)-int(j==b) for j in labels]
    queries=[tuple(sorted(rng.sample(range(n+1),2))) for _ in range(rng.randrange(2*n))]
    counts[test(n,queries,c)]+=1
assert min(counts.values())>0
print("exact graph/rank comparisons and bounded rational witnesses",counts)
print("four-quarter two-query failure and three-query certificate PASS")
