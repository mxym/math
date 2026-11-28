#!/usr/bin/env python3
"""Exact checks for ideal conductor blocks and fixed-weight parity."""
from fractions import Fraction as F
from itertools import product, combinations
from math import comb, gcd


def monomial(n,j):
    s,r=divmod(j,n)
    return tuple(0 if k!=r else (-1)**s for k in range(n))


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def mul(a,b):
    n=len(a)
    out=[0]*n
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            if (i+j)>=n:
                out[i+j-n]-=u*v
            else:
                out[i+j]+=u*v
    return tuple(out)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def phase_energy(xs):
    return sum(min(x%1,(-x)%1)**2 for x in xs)


def power_two_conductors():
    tests=0
    for n in (2,4,8):
        modulus=4 if n<=4 else 2
        pi=tuple(a-b for a,b in zip(monomial(n,0),monomial(n,1)))
        max_k=n*(modulus.bit_length()-1)
        pows=[monomial(n,0)]
        for _ in range(max_k):
            pows.append(mul(pi,pows[-1]))
        ideals=[[mul(a,monomial(n,j)) for j in range(n)] for a in pows]
        for v in product(range(modulus),repeat=n):
            if not any(v):
                continue
            k=next(k for k,u in enumerate(ideals) if all(dot(v,a)%modulus==0 for a in u))
            if F(7*k,10)>n:
                continue
            m=1
            # Contracted ramification length ell=ceil(k/e). These exact
            # branch checks use a rational upper bound for log 2.
            while True:
                d=n//m
                ell=(k+d-1)//d
                if F(7*ell,10)<=m:
                    break
                assert F(2*ell,3)>=m
                m*=2
            B=k-d*(ell-1)
            assert 1<=B<=d and ell*B<=k
            nontriv=[any(v[i+d*l]%modulus for l in range(m)) for i in range(d)]
            assert all(any(nontriv[i:i+B]) for i in range(d-B+1))
            # e^-2/4 < 1/28, log 2 > 2/3, giving a conservative RHS.
            assert phase_energy([F(a,modulus) for a in v])>=F(3*n,56*k)
            if all((2*a)%modulus==0 for a in v):
                s=[(-1)**(2*a//modulus) for a in v]
                t=sum(s[j-1]!=s[j] for j in range(n))
                assert t<=2*min(s.count(1),s.count(-1))
                assert t==0 if len(set(s))==1 else t>=2
            tests+=n
    return tests


def arbitrary_local_layers():
    count=0
    for slots in (1,2,3):
        for terms in product(product((1,2,4),(1,2),(1,2,3,5,7)),repeat=slots):
            L=max((k+e-1)//e for e,f,k in terms)
            top=[max(0,k-e*(L-1)) for e,f,k in terms]
            assert any(top)
            B=sum(f*v for (e,f,k),v in zip(terms,top))
            for (e,_,k),v in zip(terms,top):
                assert 0<=v<=e and L*v<=k
            assert L*B<=sum(f*k for e,f,k in terms)
            count+=1
    return count


def exact_split_checks():
    n,p=32,193
    a=next(a for a in range(2,p) if pow(a,n,p)==p-1)
    assert pow(a,2*n,p)==1
    bad=(a**n+1)//p
    u=(-bad*pow(n*a**(n-1),-1,p))%p
    lift=a+p*u
    assert (lift**n+1)%(p*p)==0
    tests=0
    for v in (1,3,5,7):
        # Equal top-layer exponents at the two opposite roots. They
        # contract to one residue at m=8; the first block is trivial.
        r=pow(a,v,p)
        m=8
        d=n//m
        assert pow(r,d,p)==pow(-r,d,p)
        phases=[F(pow(r,j,p)-pow(-r,j,p),p) for j in range(n)]
        blocks=[any(phases[i+d*j]%1 for j in range(m)) for i in range(d)]
        assert blocks==[False,True,False,True]
        assert phase_energy(phases)>=F(n,280)  # s=2 log p > 10
        tests+=n

        # Unequal top exponents; mixed with the exact ramified parity.
        # Here m=16 since 10<2log p and 2log p+log2<16.
        r=pow(lift,v,p*p)
        phases=[F(pow(r,j,p*p),p*p)+F(pow(-r,j,p),p)+F(1,2) for j in range(n)]
        m=16
        d=n//m
        assert pow(r,d,p)==pow(-r,d,p)
        B=1  # multiplying by p leaves exactly the top odd local factor
        assert all(any(phases[i+d*j]%1 for j in range(m)) for i in range(d))
        top=[(p*phases[j]+F(1,2))%1 for j in range(n)]
        assert top==[F(pow(r,j,p),p) for j in range(n)]
        assert phase_energy(phases)>=F(n,420)
        tests+=n
    return tests


def fixed_weight():
    count=0
    for n in (4,8,12):
        for neg in range(n+1):
            signs=[-1]*neg+[1]*(n-neg)
            for k in range(n+1):
                lhs=sum((-1)**sum(signs[i]<0 for i in S)
                        for S in combinations(range(n),k))
                rhs=sum((-1)**h*comb(neg,h)*comb(n-neg,k-h)
                        for h in range(max(0,k-(n-neg)),min(neg,k)+1))
                assert lhs==rhs
                if neg==n:
                    assert lhs==(-1)**k*comb(n,k)
                elif neg==0:
                    assert lhs==comb(n,k)
                elif 0<k<n:
                    assert abs(lhs)<comb(n,k)
                count+=1
    return count


def main():
    print(f"PASS: {power_two_conductors()} ramified phase coordinates, "
          f"{arbitrary_local_layers()} exact local-layer inventories, "
          f"{exact_split_checks()} Hensel/CRT phase rows, and "
          f"{fixed_weight()} fixed-weight sign histograms.")


if __name__=="__main__":
    main()
