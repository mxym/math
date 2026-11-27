"""Independent formula and completion verification plus all binary support pairs at n=3."""
from collections import Counter
from itertools import combinations, product
from functools import reduce
from operator import xor
from random import Random

def color_prefix(vals):
    # No matrix is constructed. Encode letters as a+2b, and accumulate
    # the parity of the prefix of second components for each first bit.
    pref=0
    f=vals[0]&1
    for t in vals[:-1]:
        pref^=t>>1
        f^=(t&1)&pref
    return f^((vals[0]&1)&(vals[2]>>1))^((vals[2]&1)&(vals[0]>>1))

def completions(n,observed,i,j,colour=color_prefix):
    d=reduce(xor,observed,0)
    V=[None]*n
    for k,t in zip((k for k in range(n) if k not in (i,j)),observed):
        V[k]=t
    out=[]
    for t in range(4):
        V[i],V[j]=t,d^t
        assert reduce(xor,V,0)==0
        out.append(colour(V))
    return out

def all_coalitions(n):
    N=n-1
    # Generate the full parity code, not the dealer's restricted free bits.
    W=Counter()
    for x in product(range(4),repeat=N):
        f=color_prefix(x+(reduce(xor,x,0),))
        W[f]+=1
    assert W=={0:2**(2*N-1),1:2**(2*N-1)}
    tests=0
    # For each maximal view use the genuinely independent direct completion
    # enumeration and sign sum test, not support projection.
    for i,j in combinations(range(n),2):
        signs=Counter()
        for z in product(range(4),repeat=n-2):
            t=sum((-1)**x for x in completions(n,z,i,j))
            assert abs(t)==2
            signs[t]+=1
            tests+=1
        assert signs=={2:4**(n-2)//2,-2:4**(n-2)//2}
    # Smaller coalitions: uniformly extend to a fixed maximal one and check
    # aggregation directly, including the absolute normalization of a view.
    partial=0
    for k in range(n-2):
        for J in combinations(range(n),k):
            more=tuple(i for i in range(n) if i not in J)
            i,j=more[-2:]
            maximal=[t for t in range(n) if t not in (i,j)]
            D={}
            for z in product(range(4),repeat=n-2):
                projection=tuple(z[maximal.index(t)] for t in J)
                L=D.setdefault(projection,[0,0])
                C=completions(n,z,i,j)
                L[0]+=C.count(0)
                L[1]+=C.count(1)
            assert len(D)==4**k and all(v>0 and w>0 and v<=3*w and w<=3*v for v,w in D.values())
            assert sum(v for v,w in D.values())==sum(w for v,w in D.values())==2**(2*N-1)
            partial+=len(D)
    return tests,partial

def binary_supports():
    good=0
    # Labels -1/0/1 mean absent and the two secrets respectively.
    for colors in product((-1,0,1),repeat=8):
        if 0 not in colors or 1 not in colors: continue
        S={i for i in range(8) if colors[i]==0}
        T={i for i in range(8) if colors[i]==1}
        if any((x^y).bit_count()<2 for x in S for y in T): continue
        if all({(v>>k)&1 for v in S}=={(v>>k)&1 for v in T} for k in range(3)): good+=1
    assert good==0
    print("all 6561 binary n=3 symbol-support colorings: no feasible one-bit scheme")

def larger_and_negative():
    rng=Random(821021)
    count=0
    for n in (10,17,33,61,128):
        for _ in range(37):
            W=[rng.randrange(4) for _ in range(n-2)]
            i,j=sorted(rng.sample(range(n),2))
            assert abs(sum((-1)**x for x in completions(n,W,i,j)))==2
            a=[rng.randrange(4) for _ in range(n-1)]
            u=a+[reduce(xor,a,0)]
            for t in range(3): a[t]^=1
            v=a+[reduce(xor,a,0)]
            assert color_prefix(u)^color_prefix(v)==1
            count+=1
    zero=(0,0)
    # Deleting the leading mixed diagonal term makes a completion line
    # affine and removes its 3:1 local split.
    def bad(V):
        return color_prefix(V)^((V[0]&1)&(V[0]>>1))
    assert sum((-1)**x for x in completions(4,zero,0,3,bad))==0
    print("independent larger-n offset and completion checks:",count,"PASS; diagonal-deletion negative control PASS")

if __name__=='__main__':
    for n in (4,5,6,7):
        print("independent direct completion n=%d: %d maximal and %d smaller views PASS" % (n,*all_coalitions(n)))
    larger_and_negative()
    binary_supports()
