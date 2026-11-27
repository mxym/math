#!/usr/bin/env python3
"""Independent literal four-translate evaluator and symbolic GF(2)[X] check."""
from hashlib import sha256

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

def quadratic_in_high_digits():
    # Univariate ring GF(2)[X], independent from finite-field operations below.
    def mul(a,b):
        z=0
        while b:
            if b&1:
                z^=a
            a<<=1
            b>>=1
        return z
    def pm(p,q):
        r=[0]*(len(p)+len(q)-1)
        for i,a in enumerate(p):
            for j,b in enumerate(q):
                r[i+j]^=mul(a,b)
        return r
    X=2
    U=X^(1<<4)
    V=U^(1<<16)
    P=[1]
    for a in (0,X,X,X,U,U,U,V,V):
        P=pm(P,[a,1])
    assert len(P)==10
    p=[0,0,0,1]
    for n in range(4,12):
        p.append(p[n-3]^mul(X,p[n-4]))
    coefficients=[]
    for shift in range(3):
        c=0
        for j,a in enumerate(P):
            c^=mul(a,p[j+shift])
        coefficients.append(c)
    D=sum(1<<i for i in (0,9,21,33,45))
    A=sum(1<<i for i in (4,10,16,22,34,46))
    assert coefficients == [D,A,mul(V,V)^mul(X,A)]
    assert D==(1^mul(1^(1<<3),mul(mul(U,U),U))^
                  mul(mul(V,V),mul(1^(1<<3),U)^mul(1<<5,mul(U,U))))
    print("PASS symbolic GF(2)[X] translation coefficients and printed reduction")

def field_check(e,m,h=None,witness=None,expected=None):
    h=e if h is None else h
    Q=1<<(2*h)
    def mul(a,b):
        c=0
        while b:
            if b&1:
                c^=a
            b>>=1
            a<<=1
            if a&Q:
                a^=m
        return c
    def pw(x,k):
        a=1
        while k:
            if k&1:
                a=mul(a,x)
            x=mul(x,x)
            k>>=1
        return a
    def S(x,j):
        y=0
        for _ in range(j):
            y^=x
            x=pw(x,4)
        return y
    seen=set()
    a=1
    for _ in range(Q-1):
        assert a and a not in seen
        seen.add(a)
        a=mul(a,2)
    assert a==1
    F4=[r for r in range(Q) if pw(r,4)==r]
    assert len(F4)==4
    n=1+3*4+3*4**2+2*4**3+4**e+4**(e+1)
    def literal(x):
        # t^4=t+x: use quotient arithmetic for the original integer power.
        def times(a,b):
            z=[0]*7
            for i,u in enumerate(a):
                for j,v in enumerate(b):
                    if u and v:
                        z[i+j]^=mul(u,v)
            for j in range(6,3,-1):
                z[j-3]^=z[j]
                z[j-4]^=mul(z[j],x)
            return tuple(z[:4])
        z=[0]*4
        for u in F4:
            a,r,k=(u,1,0,0),(1,0,0,0),n
            while k:
                if k&1:
                    r=times(a,r)
                a=times(a,a)
                k>>=1
            z=[s^v for s,v in zip(z,r)]
        assert z[1:]==[0,0,0]
        return z[0]

    assert (witness is None) or h==e>4
    if witness is None:
        sequence=range(Q)
    else:
        sequence=sorted(set(range(0,Q,199))|{0,1,witness[0],witness[1]})
    outputs={}
    deltas=0
    for x in sequence:
        u,v,E,G=S(x,2),S(x,3),S(x,e),S(x,e+1)
        D=1^pw(x,9)^pw(x,21)^pw(x,33)^pw(x,45)
        A=pw(x,4)^pw(x,10)^pw(x,16)^pw(x,22)^pw(x,34)^pw(x,46)
        R=1^mul(1^pw(x,3),pw(u,3))
        C=mul(1^pw(x,3),u)^mul(pw(x,5),pw(u,2))
        F=mul(mul(pw(u,4),v)^mul(x,v)^mul(E,G),R)
        F^=mul(mul(x,pw(v,2)),mul(1^pw(x,3),pw(u,2))^mul(pw(x,2),pw(u,3)))
        F^=mul(mul(pw(v,2),mul(E,G)),C)
        assert F==pw(v,2)^mul(mul(E,G),D)
        corr=mul(pw(x,4**e)^x,A)
        outputs[x]=literal(x)
        assert outputs[x]==F^corr
        deltas+=bool(corr)
    if h!=e:
        assert deltas==45
        print(f"negative control: e={e} in F_(4^{h}), correction nonzero at {deltas} inputs")
    else:
        assert deltas==0
        if witness is None:
            assert e==4 and set(outputs.values())==set(range(Q))
            assert sha256(bytes(outputs[x] for x in range(Q))).hexdigest()==expected
        else:
            x,w,y=witness
            assert x!=w and S(x,e)==1 and S(w,e)==S(y,e)==0
            assert outputs[x]==outputs[w]==y
        print(f"e={e} modulus={m}: {len(outputs)} original translation sums agree")

if __name__=="__main__":
    quadratic_in_high_digits()
    field_check(4,285,expected="e40b8c5ae7daf8321e0ec182d169eec921964f029df1b7a786eaa40b86c8b49e")
    field_check(4,299,expected="48bd814934d4a186c9908baa40a327d844a31ea9d9dd1ddc142a8530e127aa78")
    for e,m,w in ((5,1033,(86,771,366)), (5,1051,(10,305,972)),
                  (7,16427,(9,4147,14067)), (7,16441,(7,2633,10911)),
                  (8,65581,(14,14512,17878)), (8,65593,(9,11760,20972))):
        field_check(e,m,witness=w)
    field_check(4,67,h=3)
    print("PASS independent checks of original defining sums")
