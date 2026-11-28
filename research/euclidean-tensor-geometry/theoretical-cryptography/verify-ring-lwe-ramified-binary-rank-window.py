#!/usr/bin/env python3
"""Synthetic exact checks for repeated-root ideals and kernel valuation law."""
from collections import Counter
from fractions import Fraction as F
from itertools import product


def tpower(k):
    b=0
    s=k
    while True:
        b|=1<<s
        if not s:
            break
        s=(s-1)&k
    return b


def code_table(d):
    t=[tpower(i) for i in range(d)]
    out=[0]*(1<<d)
    for k in range(1,1<<d):
        j=(k&-k).bit_length()-1
        out[k]=out[k^(1<<j)]^t[j]
    assert len(set(out))==1<<d
    return out,t


def ideal_checks():
    duals=reps=words=0
    for d in (1,2,4,8,16):
        out,t=code_table(d)
        for r in range(d+1):
            piv=t[r:]
            dual=t[d-r:]
            assert all((a&b).bit_count()%2==0 for a,b in product(piv,dual))
            assert len(piv)+len(dual)==d
            duals+=len(piv)*len(dual)
            k=d-r
            if not k:
                continue
            D=1<<(k-1).bit_length()
            base,_=code_table(D)
            L=d//D
            repeat=sum(1<<(j*D) for j in range(L))
            im={base[i]*repeat for i in range(0,1<<D,1<<(D-k))}
            J=set(out[::1<<r])
            assert im==J
            if k<=d//2:
                half=1<<(d//2)
                assert all(a%half==a//half for a in J)
            reps+=1
            words+=len(J)
            hist=Counter(x.bit_count() for x in J)
            assert all(w%L==0 for w in hist)
            for rho in (F(1,2),F(3,5)):
                assert sum(m*rho**w for w,m in hist.items()) <= (1+rho**L)**D
    return duals,reps,words


def mul(a,b,d):
    z=0
    while a:
        p=a&-a
        z^=b<<(p.bit_length()-1)
        a-=p
    return z&((1<<d)-1)


def law_coeffs(m,n,d):
    out=[F(1)]+[F(0)]*(d-1)
    for a in range(m-n+1,m+1):
        w=F(1,2**a)
        one=[(1-w)*w**j for j in range(d)]
        out=[sum(out[i]*one[k-i] for i in range(k+1)) for k in range(d)]
    return out


def kernel_checks():
    rows=0
    for d,m,n in ((1,2,1),(1,3,2),(1,4,3),(2,2,1),
                  (2,3,2),(4,2,1),(4,3,1)):
        q=1<<d
        mult=[[mul(a,b,d) for b in range(q)] for a in range(q)]
        vecs=list(product(range(q),repeat=n))
        hist=Counter()
        for M in product(range(q),repeat=m*n):
            k=0
            for x in vecs:
                for i in range(m):
                    z=0
                    for j in range(n):
                        z^=mult[M[i*n+j]][x[j]]
                    if z:
                        break
                else:
                    k+=1
            assert k and k&(k-1)==0
            hist[k.bit_length()-1]+=1
        count=q**(m*n)
        assert sum(hist.values())==count
        for r,ex in enumerate(law_coeffs(m,n,d)):
            assert F(hist[r],count)==ex
        rankprob=F(hist[0],count)
        p=F(1)
        for a in range(m-n+1,m+1):
            p*=1-F(1,2**a)
        assert rankprob==p
        rows+=count
    return rows


def telescope():
    rows=0
    for m in range(2,20):
        for n in range(1,m):
            p=F(1)
            for a in range(m-n+1,m+1):
                p*= (1-F(1,2**a))/(1-F(1,2**(a+1)))
            assert p==(1-F(1,2**(m-n+1)))/(1-F(1,2**(m+1)))
            rows+=1
    return rows


if __name__=="__main__":
    print("PASS dual incidences, repetition classes, ideal words:",ideal_checks())
    print("PASS synthetic matrices / telescoping identities:",kernel_checks(),telescope())
