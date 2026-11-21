"""Finite algebra controls for the switch, local factors and numerical rails.
The analytic estimates are in Proof.md, not inferred from this enumeration.
"""
import math
from fractions import Fraction as F
from collections import Counter
from pathlib import Path

def need(x,msg):
    if not x: raise ValueError(msg)
def primes(n):
    return [i for i in range(2,n+1) if all(i%j for j in range(2,math.isqrt(i)+1))]
def divisors(n):
    return [i for i in range(1,n+1) if n%i==0]
def mob(n):
    k=0
    for p in primes(math.isqrt(n)):
        if n%p==0:
            n//=p;k+=1
            if n%p==0:return 0
    return (-1)**(k+(n>1))
def main():
    # Exact Möbius squarefree finite differences: the data v denote integer log coordinates.
    for xs in ([1,2,3],[2,2,5,9],[1,3,4,7,13]):
        s=sum(xs); a=Counter({0:1})
        for x in xs:
            b=a.copy()
            for u,c in a.items():b[u+x]-=c
            a=b
        for K in range(-s, s+1):
            f=lambda v: max(0,5-abs(2*v-s-K))
            raw=sum(c*f(t) for t,c in a.items())
            a1={0:1};a2={0:1}
            for i,x in enumerate(xs):
                v=a1 if i<2 else a2
                z=v.copy()
                for t,c in v.items():z[t+x]=z.get(t+x,0)-c
                v.clear();v.update(z)
            need(raw==sum(c*d*f(u+v) for u,c in a1.items() for v,d in a2.items()),'h-difference')
    # Direct expanded count of solutions per period vs the model, independently for
    # every smaller squarefree divisor pair and all admissible second sieve moduli.
    count=0
    for P in (30,42,98,110):
        for h in (1,3,5,7):
            if math.gcd(P,h)>1:continue
            ds=[n for n in range(1,16) if mob(n) and math.gcd(n,h)==1]
            qs=[n for n in range(1,13) if mob(n) and math.gcd(n,P*h)==1]
            for d in ds:
                for e in ds:
                    z=math.lcm(d,e);g=math.gcd(d,e)
                    need(math.gcd(d//g,e//g)==1 and z==g*(d//g)*(e//g),'switch')
                    for q in qs:
                        b=math.lcm(q,z)
                        found=sum(1 for n in range(z,b+1,z) if (P-h*n)%q==0)
                        need(F(found,b)==(F(1,z*q) if math.gcd(z,q)==1 else 0),'CRT')
                        count+=1
    # At zero the residual Euler factors after stripping the two joint poles.
    for p in primes(300):
        normal=(1-F(1,p))**2
        target=(1-F(1,p))/normal
        need(target==F(p,p-1),'target')
        if p>2:
            ordinary=(1-F(2,p))/normal
            need(ordinary*F(p,p-2)==1/normal,'h')
    need(.4-1.6*math.log(1.25)>.042 and (1.6*math.log(2)-1)/2>.054,'rails')
    d=Path(__file__).with_name('Proof.md').read_bytes()
    need(all(x>=32 or x==10 for x in d),'control')
    need(d.count(br'\(')==d.count(br'\)') and d.count(br'\[')==d.count(br'\]'),'TeX balance')
    print('Passed',count,'exact CRT/switch checks; factor splitting, two exponents, Euler controls.')
if __name__=='__main__': main()
