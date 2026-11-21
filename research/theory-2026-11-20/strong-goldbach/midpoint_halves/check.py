"""Exact algebra controls; the analytic estimates in Proof.md are not numerical tests."""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

def need(cond, why):
    if not cond:
        raise ValueError(why)

def parts(total, floor=1):
    if total == 0:
        yield ()
    for v in range(floor, total + 1):
        for rest in parts(total-v, v):
            yield (v,)+rest

def signed_subs(xs):
    a={0:1}
    for x in xs:
        b=dict(a)
        for t,c in a.items():
            b[t+x]=b.get(t+x,0)-c
        a=b
    return a

def sinh_products(xs,K):
    # coefficients multiplied by k!, independent of signed_subs
    a=[1]+[0]*K
    for x in xs:
        a=[sum(comb(k,m)*2*x**m*a[k-m] for m in range(1,k+1,2)) for k in range(K+1)]
    return a

def main():
    count=0; witnesses=[]
    for m in range(1,21):
        for xs in parts(m):
            sd=signed_subs(xs)
            sp=sinh_products(xs,10)
            for k in range(1,11):
                raw=sum(c*max(0,m-2*t)**k for t,c in sd.items())
                half=raw if (len(xs)-k)%2==0 else 0
                need(2*half==sp[k],(xs,k,half,sp[k]))
                need(half>=0 and (len(xs)<=k or half==0),(xs,k))
                if len(xs)==2 and k==2:
                    need(half==4*xs[0]*xs[1],('two',xs))
                if len(xs)==3 and k==3:
                    need(half==24*xs[0]*xs[1]*xs[2],('three',xs))
                if k==2 and len(xs)%2 and raw<0 and len(witnesses)<2:
                    witnesses.append((xs,raw))
                count+=1
    need(witnesses, 'no signed control')
    # Aggregate simplex mean directly by partition of degree into odd multiplicities.
    for k in range(1,31):
        mass=F(0)
        for xs in parts(k):
            if any(x%2==0 for x in xs):
                continue
            mult=1
            for x in set(xs):
                mult*=factorial(xs.count(x))
            q=F(k,2*mult)
            for x in xs:
                q*=F(2,x)
            mass+=q
        need(mass==k,(k,mass))
    print('Exact checks:',count,'fraction-free profile/degree cases, degrees 1..30 integrated.')
    print('Signed opposite-half examples (rational profile numerator; not prime samples):',witnesses)
    doc=Path(__file__).with_name('Proof.md').read_bytes()
    need(not any(c<32 and c!=10 for c in doc),'control byte in proof')
    need(doc.count(br'\(')==doc.count(br'\)') and doc.count(br'\[')==doc.count(br'\]'),'TeX pairs')
if __name__=='__main__':
    main()
