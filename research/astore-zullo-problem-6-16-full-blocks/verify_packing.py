#!/usr/bin/env python3
"""Verify small projective-line packings and their determinant polynomials."""
from functools import lru_cache
from itertools import permutations, product
from math import gcd

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

class Field:
    # Prime-field polynomial model. mod contains the constant-to-lowest
    # monic polynomial coefficients, omitting its leading coefficient.
    def __init__(self,p,mod,q):
        self.p,self.q,self.d=p,q,len(mod)
        self.Q=p**self.d
        self.E=tuple(range(self.Q))
        self.rep=[[a//p**i%p for i in range(self.d)] for a in self.E]
        self.add=[[self.encode([(x+y)%p for x,y in zip(a,b)])
                   for b in self.rep] for a in self.rep]
        self.neg=[self.encode([-i%p for i in a]) for a in self.rep]
        def multiply(a,b):
            c=[0]*(2*self.d-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b):
                    c[i+j]+=x*y
            for i in range(len(c)-1,self.d-1,-1):
                x=c[i]%p
                for j,y in enumerate(mod):
                    c[i-self.d+j]-=x*y
            return self.encode([x%p for x in c[:self.d]])
        self.mul=[[multiply(a,b) for b in self.rep] for a in self.rep]
        self.inv=[0]+[self.mul[x].index(1) for x in self.E[1:]]
        self.F=tuple(a for a in self.E if self.power(a,q)==a)
        assert len(self.F)==q
        m=0
        v=1
        while v<self.Q:
            v*=q
            m+=1
        assert v==self.Q
        self.m=m
        self.theta=(self.Q-1)//(q-1)
        self.frob=[tuple(self.power(x,q**s) for x in self.E) for s in range(m)]
        self.norm=[self.power(x,self.theta) for x in self.E]
    def encode(self,a):
        return sum(x*self.p**i for i,x in enumerate(a))
    def power(self,x,d):
        y=1
        while d:
            if d&1:
                y=self.mul[y][x]
            x=self.mul[x][x]
            d>>=1
        return y

def coefficients(F,a):
    # Sparse polynomial via independent Leibniz expansion. Index is the
    # tuple of Frobenius-coordinate exponents, not a univariate exponent.
    m=F.m
    Q=range(m)
    out={}
    Z=(0,)*m
    for s in permutations(Q):
        invs=sum(s[i]>s[j] for i in Q for j in Q if i<j)
        terms=[(Z,1 if invs%2==0 else F.neg[1])]
        for i,j in enumerate(s):
            b=F.neg[F.frob[i][a[(j-i)%m]]]
            ts=[]
            for e,c in terms:
                if b:
                    ts.append((e,F.mul[c][b]))
                if i==j:
                    v=list(e)
                    v[i]=1
                    ts.append((tuple(v),c))
            terms=ts
        for e,c in terms:
            out[e]=F.add[out.get(e,0)][c]
    return {e:c for e,c in out.items() if c}

def multiply(F,A,B):
    C={}
    for a,x in A.items():
        for b,y in B.items():
            m=tuple(i+j for i,j in zip(a,b))
            C[m]=F.add[C.get(m,0)][F.mul[x][y]]
    return {m:x for m,x in C.items() if x}

def eval_multi(F,P,z):
    value=0
    for e,a in P.items():
        R=F.power(z,sum(x*F.q**i for i,x in enumerate(e)))
        value=F.add[value][F.mul[a][R]]
    return value

def slopes(F,a):
    N=[]
    active=[(s,b) for s,b in enumerate(a) if b]
    for x in F.E[1:]:
        y=0
        for s,b in active:
            y=F.add[y][F.mul[b][F.frob[s][x]]]
        N.append(F.mul[y][F.inv[x]])
    return set(N)

def mask(S):
    return sum(1<<x for x in S)

def exact_covers(F,options):
    by=[tuple(c for c in options if c>>i&1) for i in F.E]
    @lru_cache(None)
    def rec(rest):
        if not rest:
            return ((),)
        j=(rest&-rest).bit_length()-1
        return tuple((x,)+tail for x in by[j] if rest&x==x for tail in rec(rest^x))
    return rec((1<<F.Q)-2)

def verify(F,exhaustive):
    q,m=F.q,F.m
    zero=(0,)*m
    top=(1,)*m
    fibers={r:{x for x in F.E[1:] if F.norm[x]==r} for r in F.F[1:]}
    assert len(fibers)==q-1 and {len(s) for s in fibers.values()}=={F.theta}
    opts={}
    if exhaustive:
        for a in product(F.E,repeat=m):
            S=slopes(F,a)
            if len(S)==F.theta and 0 not in S:
                opts.setdefault(mask(S),[]).append(a)
        covers=exact_covers(F,opts)
        assert len(covers)==1 and set(covers[0])=={mask(S) for S in fibers.values()}
        for S in fibers.values():
            # Check every graph subspace representing a saturated member.
            for a in opts[mask(S)]:
                supp=[i for i,b in enumerate(a) if b]
                assert len(supp)==1 and gcd(supp[0],m)==1

    C={zero:1}
    for j,(r,S) in enumerate(fibers.items()):
        s=[k for k in range(1,m) if gcd(k,m)==1][j%sum(gcd(k,m)==1 for k in range(1,m))]
        a=[0]*m
        a[s]=min(S)
        assert slopes(F,a)==S
        P=coefficients(F,a)
        assert P=={top:1,zero:F.neg[r]}
        assert {z for z in F.E if eval_multi(F,P,z)==0}==S
        C=multiply(F,C,P)
    assert C=={tuple(q-1 for _ in top):1,zero:F.neg[1]}

    # Negative control: a nonzero translate of a norm fiber avoids 0,
    # is itself scattered, but cannot replace a member of the partition.
    r=next(r for r in F.F[1:] if r!=F.norm[F.neg[1]])
    a=[0]*m
    a[0]=1
    a[1]=min(fibers[r])
    S=slopes(F,a)
    assert 0 not in S and len(S)==F.theta and S not in fibers.values()
    P=coefficients(F,a)
    assert {z for z in F.E if eval_multi(F,P,z)==0}==S
    assert len(P)>2
    if exhaustive:
        assert all(mask(S) not in e for e in covers)
    if m==4:
        bad=[0]*m
        bad[2]=1
        assert len(slopes(F,bad))<F.theta
        assert len(coefficients(F,bad))>2

    extra = f"; {len(opts)} candidate slope sets, exactly 1 cover" if exhaustive else ""
    print(f"q={q}, m={m}: determinant/norm packing checked{extra}; controls PASS")

if __name__=="__main__":
    for q,p,poly,ex in (
        (3,3,[1,0],True),
        (4,2,[1,1,0,0],True),
        (5,5,[2,0],True),
        (7,7,[1,0],True),
        (3,3,[1,2,0],True),
        (4,2,[1,1,0,0,0,0],False),
        (3,3,[2,1,0,0],False),
    ):
        verify(Field(p,poly,q),ex)
    print("PASS independent finite packing checks")
