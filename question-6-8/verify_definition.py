#!/usr/bin/env python3
"""Independent carryless verification of the literal translation identity."""
if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

def check(e,m,domain=None):
    h=e if domain is None else domain
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
    def S(x,e):
        z=0
        for j in range(e):
            z^=x
            x=pw(x,4)
        return z
    P=set()
    a=1
    for i in range(Q-1):
        assert a and a not in P
        P.add(a)
        a=mul(a,2)
    assert a==1
    F4=tuple(x for x in range(Q) if pw(x,4)==x)
    assert len(F4)==4
    n=1+2*4+4**2+2*4**3+2*4**(e+1)
    def defining(x):
        def times(a,b):
            z=[0]*7
            for i,u in enumerate(a):
                for j,v in enumerate(b):
                    if u and v:
                        z[i+j]^=mul(u,v)
            for i in range(6,3,-1):
                z[i-3]^=z[i]
                z[i-4]^=mul(z[i],x)
            return tuple(z[:4])
        z=[0]*4
        for u in F4:
            a,r,k=(u,1,0,0),(1,0,0,0),n
            while k:
                if k&1:
                    r=times(a,r)
                a=times(a,a)
                k>>=1
            for i in range(4):
                z[i]^=r[i]
        assert z[1:]==[0,0,0]
        return z[0]

    if h==e and e<=4:
        seq=range(Q)
    elif h==e:
        seq=sorted(set(range(0,Q,199))|{0,1}|
            {(6,8137):{58,873},(8,131053):{6202,4686}}[e,m])
    else:
        seq=range(Q)
    outputs={}
    off=0
    for x in seq:
        u,v,t=S(x,2),S(x,3),S(x,e)
        t2=pw(t,2)
        raw=mul(x,v)^mul(pw(u,4),v)^pw(u,5)^mul(u,v)^t2^mul(pw(x,4),u)^mul(mul(pw(x,2),u),t2)^mul(mul(u,pw(v,2)),t2)
        printed=pw(x,32)^mul(t2,1^pw(u,9))
        literal=pw(x,32)^mul(pw(S(x,e+1)^x,2),1^pw(u,9))
        correction=mul(pw(pw(x,4**e)^x,2),1^pw(u,9))
        assert raw==printed
        assert literal==defining(x)==printed^correction
        off+=bool(correction)
        outputs[x]=literal
    if h==e:
        assert off==0
        if e==4:
            assert len(set(outputs.values()))==256
        if e==6:
            assert outputs[58]==outputs[873]==2035
        if e==8:
            assert outputs[6202]==outputs[4686]==28143
        print(f"e={e} modulus={m}: {len(outputs)} literal defining sums agree")
    else:
        assert off>0  # Printed and literal polynomials need not agree off K.
        print(f"e={e} evaluated in F_(4^{h}) (modulus {m}): correction nonzero at {off} inputs")

if __name__=="__main__":
    for e,m in ((3,67),(4,285),(4,501),(6,8137),(8,131053)):
        check(e,m)
    check(4,67,domain=3)
    print("PASS independent literal-definition checks")
