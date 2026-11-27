#!/usr/bin/env python3
"""Separate carryless and quotient-ring replay, without logs or imports from other verifier."""
if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

def check(e,mod):
    Q = 1 << (2*e)
    def m(a,b):
        z = 0
        while b:
            if b & 1:
                z ^= a
            b >>= 1
            a <<= 1
            if a & Q:
                a ^= mod
        return z
    def pw(a,k):
        t=1
        while k:
            if k&1:
                t=m(t,a)
            a=m(a,a)
            k>>=1
        return t
    # Verify field rather than assuming the supplied modulus is irreducible.
    E, a = set(), 1
    for _ in range(Q-1):
        assert a not in E and a != 0
        E.add(a)
        a=m(a,2)
    assert a == 1 and len(E)==Q-1

    def S(x,j):
        r=0
        for _ in range(j):
            r ^= x
            x=pw(x,4)
        return r
    F4 = tuple(a for a in range(Q) if pw(a,4)==a)
    assert len(F4)==4
    n = 1+4**(e-2)+4**(e-1)+2*4**e

    def defining(x):
        def times(a,b):
            v=[0]*7
            for i,t in enumerate(a):
                for j,w in enumerate(b):
                    if t and w:
                        v[i+j]^=m(t,w)
            for i in range(6,3,-1):
                v[i-3]^=v[i]
                v[i-4]^=m(v[i],x)
            return tuple(v[:4])
        def Rpower(a,k):
            v=(1,0,0,0)
            while k:
                if k&1:
                    v=times(v,a)
                a=times(a,a)
                k>>=1
            return v
        z=[0]*4
        for b in F4:
            for j,w in enumerate(Rpower((b,1,0,0),n)):
                z[j]^=w
        assert z[1:] == [0,0,0]
        return z[0]

    def printed(x):
        T=S(x,e)
        B=S(x,e-1)
        return m(B,T)^m(B,pw(S(x,2),4**(e-2)))^pw(T,2)

    values = {}
    xset = tuple(range(Q)) if e<=5 else tuple(x for x in range(Q) if x%193==0 or x<16)
    for x in xset:
        y=pw(x,4**(e-2))
        T=S(x,e)
        assert y==0 or pw(y,16)==x  # inverse Frobenius on K
        h=pw(y,8)^pw(y,5)^m(y,S(y,e))
        f=defining(x)
        assert f == h == printed(x) == m(S(x,e-1),S(x,e-2))^pw(T,2)
        values[x]=f
    if e==3:
        assert len(values)==len(set(values.values()))==64
    if e==4:
        assert values[0]==values[1]==0
    if (e,mod)==(5,2041):
        y,z=45,126
        x,w=pw(y,16),pw(z,16)
        assert x!=w and values[x]==values[w]==976
        x,w=pw(59,16),pw(190,16)
        assert x!=w and values[x]==values[w]==927
    if (e,mod)==(7,32743):
        y,z=59,326
        x,w=pw(y,16),pw(z,16)
        assert x!=w and defining(x)==defining(w)==11628
        x,w=pw(15728,16),pw(475,16)
        assert x!=w and defining(x)==defining(w)==214
    print(f"e={e} modulus={mod}: {len(xset)} literal defining sums agree with formulas")

if __name__=="__main__":
    for e,mod in ((3,67),(3,115),(4,285),(5,2041),(7,32743)):
        check(e,mod)
    print("PASS independent carryless quotient-ring replay")
