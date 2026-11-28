#!/usr/bin/env python3
"""Exact local checks for FactorErdosStrausSinglePrimeSieve.md."""

from fractions import Fraction
from math import gcd, isqrt, lcm


def check(test,message):
    if not test:
        raise AssertionError(message)


def divisors(n):
    lo=[d for d in range(1,isqrt(n)+1) if n%d==0]
    return lo + [n//d for d in reversed(lo) if d*d!=n]


def prime_sieve(n):
    P=bytearray(b'\x01')*(n+1)
    P[:2]=b'\x00\x00'
    for q in range(2,isqrt(n)+1):
        if P[q]:
            P[q*q::q]=b'\x00'*(((n-q*q)//q)+1)
    return [i for i in range(n+1) if P[i]]


def snapshot(q):
    # Brute projections of the seven displayed Elsholtz--Tao families.
    unit=list(range(1,4*q,4))
    first,second,third,fourth,II1,II2,II3=[set() for j in range(7)]
    M=4*q
    # Every factor that occurs inside a modulus multiple of 4 divides q.
    for u in (1,q):
        for v in (1,q):
            if q%(u*v):
                continue
            for f in divisors(4*u*u*v+1):
                if f%4==3:
                    first.update(n%q for n in unit if (n+f)%(4*u*v)==0)
            for g in divisors(u+v):
                if gcd(g,4*u*v)==1 and g%4==3:
                    fourth.update(n%q for n in unit if (n*g+1)%(4*u*v)==0)
                    II1.update(n%q for n in unit if (n+g)%(4*u*v)==0)
            for g in divisors(M):
                if gcd(g,4*u*v)!=1 or M%lcm(g,4*u*v):
                    continue
                # Same parameter positions u,v are renamed in the three formulas.
                second.update(n%q for n in unit if (n+g)%(4*u*v)==0
                              and (n*u+v)%g==0)
                third.update(n%q for n in unit if (n+g)%(4*u*v)==0
                             and (n*n+4*u*u*v)%g==0)
                II3.update(n%q for n in unit if M%(4*u*v*g)==0
                            and (n+4*u*u*v+g)%(4*u*v*g)==0)
    for f in divisors(M):
        if f%4!=3:
            continue
        for a in divisors((f+1)//4):
            for d in divisors((f+1)//(4*a)):
                II2.update(n%q for n in unit if (n+4*a*a*d)%f==0)
    return first,second,third,fourth,II1,II2,II3


def local(q):
    first,second,third,fourth,II1,II2,II3=snapshot(q)
    F={f for f in divisors(4*q+1) if f%4==3}
    G={g for g in divisors(q+1) if g%4==3}
    A={-f%q for f in F}
    B={-g%q for g in G}
    C={-(q+1)//g%q for g in G}
    check((first,II1,fourth)==(A,B,C),(q,'three labels'))
    check(len(A)==len(F) and len(B)==len(C)==len(G) and not (B&C),(q,'labels injective'))
    common=q%3==2
    check(A&B==({-3%q} if common else set()),(q,'first overlap'))
    check(A&C==({-(q+1)//3%q} if common else set()),(q,'second overlap'))
    check(len(A|B|C)==len(F)+2*len(G)-2*common,(q,'three-family union'))
    if q%4==1:
        check(not (second|third|II2|II3),(q,'no extra families'))
        D=set()
    else:
        h=(q+1)//4
        D={-4*d%q for d in divisors(h*h)}
        check(II2==D and second=={-1%q} and not third and II3=={-4%q},
              (q,'additional families'))
        check((second|II3)<=D,(q,'additional families absorbed'))
    check(all(pow(a,(q-1)//2,q)==q-1 for a in (A|B|C|D)),(q,'all nonresidues'))

    for f in F:
        n=4*q-f
        k=(4*q+1)//f
        a=(n+f)//(4*q)
        b=a*k-1
        den=(a*q,a*b*q,b*q*n)
        check(0<den[0]<den[1]<den[2],(q,'I1 positivity'))
        check(sum(Fraction(1,z) for z in den)==Fraction(4,n),(q,'I1 decomposition'))
    for g in G:
        c=(q+1)//g
        n=4*q-g
        d=(n+g)//(4*q)
        den=(q*d,c*d*n,q*c*d*n)
        check(0<den[0]<den[1]<den[2] and sum(Fraction(1,z) for z in den)==Fraction(4,n),
              (q,'II1 decomposition'))
        n=-pow(g,-1,4*q)%(4*q)
        d=(n*g+1)//(4*q)
        den=(c*d,q*c*d,q*d*n)
        check(0<den[0]<den[1]<den[2] and sum(Fraction(1,z) for z in den)==Fraction(4,n),
              (q,'I4 decomposition'))


def small_ratio(numerator,q):
    m=(q+1)//numerator
    seen={}
    for u in divisors(m):
        if u>isqrt(q):
            continue
        count=0
        for a in divisors(u):
            h=u//a
            if gcd(a,h)>1:
                continue
            count+=1
            r=-a*pow(h,-1,q)%q
            check(r and r not in seen,(numerator,q,'ratio uniqueness'))
            seen[r]=a,h
            d=m//u
            for j in (0,1):
                n=r+q*j
                check((n+numerator*a*a*d)%q==0,(numerator,q,'equivalent congruence'))
                e=(n+numerator*a*a*d)//q
                b=h*e-a
                check(b>0,(numerator,q,'positive'))
                den=(a*b*d,a*h*d*n,b*h*d*n)
                check(sum(Fraction(1,z) for z in den)==Fraction(numerator,n),
                      (numerator,q,'Type II decomposition'))
        divs=divisors(u)
        squarefree=sum(all(t%(p*p) for p in prime_sieve(isqrt(t))) for t in divs)
        check(count==squarefree,(numerator,q,'count 2^omega'))
    if numerator==4:
        check(all(pow(r,(q-1)//2,q)==q-1 for r in seen),(q,'ratio nonresidues'))
    return len(seen)


def check_euler():
    for p in prime_sieve(200):
        for k in (4,7,12,25,77):
            b=Fraction(1) if k%p==0 else Fraction(p,p-1)
            L=(1-Fraction(1,p))**2*(1+2*b/(p-1))
            R=1+Fraction(-1 if k%p==0 else 1,p*p)
            check(L==R,(p,k,'double Euler factor'))
    # For numerator 4, c_4=(1/2)(3/5) zeta(2)/zeta(4), gamma=c_4/8.
    check(Fraction(1,2)*Fraction(3,5)/8*15==Fraction(9,16),'gamma_4*pi^2')
    check(Fraction(9,16)/16==Fraction(9,256),'large-sieve constant cube')


def main():
    P=prime_sieve(1200)
    for q in P:
        if 7<q<700:
            local(q)
    total=0
    for k in range(2,16):
        for q in P:
            if q>max(7,k) and (q+1)%k==0:
                total+=small_ratio(k,q)
    check_euler()
    print('PASS all seven local families at',sum(7<q<700 for q in P),'auxiliary primes')
    print('PASS',total,'injective ratio classes and first two Type II solutions per class')


if __name__=='__main__':
    main()
