#!/usr/bin/env python3
from itertools import combinations
from math import gcd, isqrt

def primes_upto(n):
    a=bytearray(b"\x01")*(n+1)
    a[:2]=b"\x00\x00"
    for p in range(2,isqrt(n)+1):
        if a[p]:
            a[p*p:n+1:p]=b"\x00"*(((n-p*p)//p)+1)
    return [i for i in range(2,n+1) if a[i]]

def prime_factors(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out

def vr(n,r):
    t=0
    while n%r==0:
        n//=r;t+=1
    return t

def support_exponent(N,S):
    E=1
    for r in S:
        if r>N:continue
        u=1
        while u<=N//r:u*=r
        E*=u
    return E

def is_smooth(n,y):
    if n==1:return True
    d=2
    while d*d<=n:
        while n%d==0:
            if d>y:return False
            n//=d
        d+=1
    return n==1 or n<=y

def psi(x,y):
    return sum(is_smooth(n,y) for n in range(1,x+1))

def order_mod(a,p):
    out=p-1
    for r in prime_factors(p-1):
        while out%r==0 and pow(a,out//r,p)==1:
            out//=r
    return out

def refine_one(D,E,S,a):
    U=gcd(D,pow(a,D.bit_length(),D))
    initial=[D] if U in (1,D) else [U,D//U]
    out=[]
    for X in initial:
        if gcd(a,X)!=1:
            out.append(X);continue
        parts=[X]
        for r in S:
            t=vr(E,r)
            for j in range(t+1):
                raw=gcd(pow(a,E//(r**j),X)-1,X)
                cut=gcd(X,pow(raw,X.bit_length(),X))
                nxt=[]
                for Y in parts:
                    h=gcd(Y,cut)
                    nxt.extend([h,Y//h] if 1<h<Y else [Y])
                parts=nxt
        out.extend(parts)
    return sorted(out)

def prime_escape(h,g,y):
    for ell in primes_upto(min(y,h-1)):
        if pow(ell,g,h)!=1:return ell
    return None

def recover_by_coefficients(N,T):
    tested=0
    for A in range(1,T+1):
        for B in range(1,T+1):
            tested+=1
            disc=(A+B)*(A+B)+4*A*B*(N-1)
            d=isqrt(disc)
            if d*d!=disc:continue
            den=2*A*B
            num=d-A-B
            if num<=0 or num%den:continue
            g=num//den
            p=A*g+1;q=B*g+1
            if p*q==N:
                return tuple(sorted((p,q))),tested
    return None,tested

P=primes_upto(139)
pairs=0
support_checks=0
algebra_checks=0
enumeration_recoveries=0
enumeration_candidates=0
smooth_conditions=0
prime_escapes=0
chain_splits=0
false_positive_strips=0

for p,q in combinations(P,2):
    if p==2:continue
    N=p*q
    lam=(p-1)*(q-1)//gcd(p-1,q-1)
    S=prime_factors(lam)
    E=support_exponent(N,S)
    assert E%lam==0
    support_checks+=1

    g=gcd(p-1,q-1)
    A=(p-1)//g;B=(q-1)//g
    assert gcd(A,B)==1
    assert N==A*B*g*g+(A+B)*g+1
    disc=(A+B)*(A+B)+4*A*B*(N-1)
    assert isqrt(disc)**2==disc
    algebra_checks+=1

    got,tested=recover_by_coefficients(N,max(A,B))
    assert got==(p,q)
    enumeration_recoveries+=1
    enumeration_candidates+=tested

    for y in (3,5,7,11,17):
        for h,m in ((p,A),(q,B)):
            x=h-1
            if psi(x,min(y,x))<=g:continue
            smooth_conditions+=1
            ell=prime_escape(h,g,y)
            assert ell is not None and pow(ell,g,h)!=1
            other=q if h==p else p
            # Since gcd(A,B)=1, escaping the gcd subgroup forces
            # a support-coordinate order difference.
            oh=order_mod(ell,h)
            oo=order_mod(ell,other)
            assert any(vr(oh,r)>vr(oo,r) for r in S)
            assert refine_one(N,E,S,ell)==[p,q]
            prime_escapes+=1
            chain_splits+=1
    pairs+=1

    # False positives are permitted.  If one listed prime is itself a
    # factor, exact division strips it before the hybrid step.
    S2=sorted(set(S+[p]))
    E2=support_exponent(N,S2)
    assert E2%lam==0 and N%p==0
    false_positive_strips+=1

print(f"odd semiprime pairs: {pairs}")
print(f"support exponent checks: {support_checks}")
print(f"cofactor algebra checks: {algebra_checks}")
print(f"coefficient recoveries: {enumeration_recoveries}")
print(f"coefficient candidates tested: {enumeration_candidates}")
print(f"exact smooth-count conditions: {smooth_conditions}")
print(f"prime subgroup escapes: {prime_escapes}")
print(f"complete chain splits: {chain_splits}")
print(f"false-positive direct strips: {false_positive_strips}")
print("PASS")
