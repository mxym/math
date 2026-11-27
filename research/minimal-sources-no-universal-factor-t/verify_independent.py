#!/usr/bin/env python3
"""Exact conditional message laws in a toy six-party execution."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from operator import xor
from functools import reduce


Q=8
N=6
T=2
D=(0,1)
WORD=Q.bit_length()-1
alist=(1,2,3,4,5,6)
sites=(0,)+alist
interp_ids=(2,4,5)
zsum=lambda xs: reduce(xor,xs,0)
# Use the GF(8) antirecurrence x^3=x+1 and logarithm arithmetic,
# independent of the coefficient-matrix verifier.
powers=(1,2,4,3,6,7,5)
assert set(powers)==set(range(1,Q))
logs={x:i for i,x in enumerate(powers)}
def mult(a,b):
    return powers[(logs[a]+logs[b])%7] if a and b else 0


def muls(vals):
    out=1
    for a in vals: out=mult(out,a)
    return out


@lru_cache(None)
def weights(xs,target):
    return tuple(muls(target^x0 for x0 in xs if x0!=x) for x in xs),tuple(
           powers[(-logs[muls(x^x0 for x0 in xs if x0!=x)])%7] for x in xs)


def at(xs,vals,u):
    num,den=weights(xs,u)
    return zsum(mult(y,mult(a,b)) for y,a,b in zip(vals,num,den))


def evals(xs,vals):
    return tuple(at(xs,vals,u) for u in sites)


def pack(vals):
    return sum(y<<(WORD*i) for i,y in enumerate(vals))


def unpack(z):
    return tuple((z>>(WORD*i))&(Q-1) for i in range(len(sites)))


def rule(bits):
    return (bits[0]&bits[1])^zsum(bits[2:])


def serial(C):
    # Fix each corrupt dealer tape and every separate honest-to-C setup
    # packet. Generate the true conditional tables from arbitrary cut words.
    basis=((1,1,0,1,0),(0,1,1,0,1))
    candidates=list(product(range(2),repeat=N-1))
    adj=lambda a,i:(0 if i==0 else a[i-1])^(0 if i==N-1 else a[i])
    R=[]
    for d,a in zip(D,basis):
        if d in C:
            R.append((a,))
        else:
            p=tuple(adj(a,i) for i in C)
            R.append(tuple(v for v in candidates if tuple(adj(v,i) for i in C)==p))
    J=tuple(sorted({j for i in C for j in (i,i+1) if 1<=j<N}))

    @lru_cache(None)
    def calls(u):
        hist=Counter()
        for masks in product(*R):
            after=0
            observed=[]
            for i in range(N):
                after^=u[i]^zsum(adj(a,i) for a in masks)
                if i+1 in J: observed.append(after)
            assert after==zsum(u)
            hist[after,tuple(observed)]+=1
        return hist
    return calls


def one_fixture(C):
    # For every bit input the following is a positive-probability
    # conditional setup view (for the corresponding corrupt inputs).
    # Honest input dealers' polynomials vary with the hidden constant
    # while the evaluations delivered to C stay fixed.
    points=tuple(alist[i] for i in C)
    msize=len(points)
    assert msize==T
    X0=(0,)+points
    l0_data=[(5,2),(4,7)]
    h0_data=[(6,7),(2,3)]
    both_dealers=Counter({0:1})
    for d in D:
        random_free=tuple(p for p in alist if p not in points)[:2]
        polys=Counter()
        for extra in product(range(Q),repeat=3):
            xs=points+(0,)+random_free
            ys=h0_data[d]+extra
            h=evals(xs,ys)
            assert tuple(h[i+1] for i in C)==h0_data[d]
            polys[pack(h)]+=1
        assert len(polys)==Q**3 and set(polys.values())=={1}
        if d in C:
            p=next(iter(polys))
            polys=Counter({p:1})
        both_dealers=convolve(both_dealers,polys)
    if len(set(D)-set(C)):
        assert len(both_dealers)==Q**3
        assert len(set(both_dealers.values()))==1
    else:
        assert len(both_dealers)==1
    low_vals=tuple(a^b for a,b in zip(*l0_data))
    assert len(low_vals)==T
    maskinfo=[]
    for Hkey,mass in both_dealers.items():
        H=unpack(Hkey)
        Low=evals(X0,(H[0],)+low_vals)
        assert tuple(Low[i+1] for i in C)==low_vals
        tpoints=tuple(alist[i] for i in interp_ids)
        nums,dens=weights(tpoints,0)
        lm=[0]*N
        for i,v,w in zip(interp_ids,nums,dens):
            lm[i]=(mult(Low[i+1],mult(v,w)))&1
        assert zsum(lm)==(H[0]&1)
        maskinfo.append((H,tuple(lm),mass))
    calls=serial(C)
    clusters={}
    tests=0
    changed=0
    for x in product(range(2),repeat=N):
        inputsp=[]
        for d in D:
            # Corrupt owners' fixed complete coefficient tape is known.
            # Otherwise interpolate the fixed incoming packets and x_d.
            if d in C:
                inputsp.append(tuple(x[d]^mult(2+d,a)^mult(6-d,mult(a,a))
                                     for a in sites))
            else:
                inputsp.append(evals(X0,(x[d],3+d,4+d)))
        A,B=inputsp
        out=rule(x)
        full=Counter()
        for H,lm,mass in maskinfo:
            V=tuple(mult(a,b)^h for a,b,h in zip(A,B,H))
            u=tuple(lm[i]^(x[i] if i>=2 else 0) for i in range(N))
            for (Y,path),copies in calls(u).items():
                assert Y^(V[0]&1)==out
                full[V[1:],Y,path]+=mass*copies
        key=tuple(x[i] for i in C),out
        if key in clusters:
            first,a=clusters[key]
            assert full==a
            if (x[0]&x[1])!=(first[0]&first[1]): changed+=1
            tests+=1
        else:
            clusters[key]=(x,full)
    return tests,changed


def convolve(A,B):
    out=Counter()
    for a,s in A.items():
        for b,t in B.items(): out[a^b]+=s*t
    return out


def reductions():
    cases=0
    for n,t in ((8,3),(10,4),(12,5)):
        for x in product(range(2),repeat=n):
            if x[0]==x[1]==0:assert rule(x)==zsum(x[2:])
            if not any(x[2:]):assert rule(x)==x[0]*x[1]
            cases+=1
        others=tuple(range(2,n))
        for k in range(t-1):
            for C in combinations(others,k):
                old=set(C)
                if 2 in old:old.add(0)
                if 3 in old:old.add(1)
                assert len(old)<=t
        # One disjoint equal-size grouping, with 0 and 1 in opposite halves.
        A={0,*range(2,n//2+1)}
        assert len(A)==n//2 and 1 not in A
    print(f"independent PASS: {cases} Boolean restrictions and coalition-host reduction controls")


if __name__=="__main__":
    results=[one_fixture(C) for C in ((0,1),(0,3),(2,4),(1,5))]
    assert all(n==56 for n,k in results)
    assert any(k for n,k in results)
    print(f"independent PASS: {sum(n for n,k in results)} direct conditional transcript equalities, {sum(k for n,k in results)} across different hidden products")
    print("independent PASS: all-source-corrupt, one-honest-source, and two-honest-source branches")
    reductions()
