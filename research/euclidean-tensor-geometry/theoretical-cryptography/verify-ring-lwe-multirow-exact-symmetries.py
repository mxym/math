#!/usr/bin/env python3
"""Exact checks for dyadic multirow relabeling rigidity."""

from fractions import Fraction as F
from itertools import product,permutations
from math import gcd


def add(a,b,q):
    return tuple((u+v)%q for u,v in zip(a,b))


def mul(a,b,q):
    d=len(a)
    out=[0]*d
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            r=i+j
            out[r%d]+=(1 if r<d else -1)*u*v
    return tuple(x%q for x in out)


def verify_short_unit_inverses():
    cases=0
    for d in (2,4,8,16,32,64):
        for q in (3,5,9,15,21,25):
            one=(1,)+(0,)*(d-1)
            zero=(0,)*d
            for i in range(1,d):
                m=d//gcd(i,d)
                for e in (-1,1):
                    v=tuple(e%q if j==i else 0 for j in range(d))
                    r,s=one,zero
                    for _ in range(m):
                        s=add(s,r,q)
                        r=mul(r,v,q)
                    assert r==(q-1,)+(0,)*(d-1)
                    f=add(one,tuple(-x%q for x in v),q)
                    assert mul(f,s,q)==(2,)+(0,)*(d-1)
                    cases+=1
    return cases


def verify_first_character_pairs():
    items=0
    for q,d in ((3,1),(3,2),(3,4),(3,8),(5,4),(9,2),(15,2)):
        zero=(0,)*d
        for a in product(range(q),repeat=d):
            if a==zero:
                continue
            bar=a[:1]+tuple(-x%q for x in reversed(a[1:]))
            freqs=set()
            for j in range(d):
                e=tuple(int(i==j) for i in range(d))
                w=mul(bar,e,q)
                assert w!=zero and tuple(-x%q for x in w)!=w
                freqs.add(w)
                freqs.add(tuple(-x%q for x in w))
            assert len(freqs)==2*d
            items+=1
    return items


def verify_mass():
    tests=0
    for n,k in product((2,3,5,8,9),range(1,5)):
        z=o=0
        for combo in product(range(n),repeat=k):
            count=sum(x!=0 for x in combo)
            z+=count==0
            o+=count==1
        assert F(z,n**k)==F(1,n)**k
        assert F(o,n**k)==k*(1-F(1,n))*F(1,n)**(k-1)
        tests+=1
    return tests


def verify_couplings_and_increment():
    gluing=inc=0
    for a,b,c in product(range(1,4),repeat=3):
        p=tuple((F(j,4),1-F(j,4)) for j in (a,b,c))
        mu=tuple(sum(p[s][x] for s in range(3))/3 for x in range(2))
        eta=tuple(tuple(p[s][x]/(3*mu[x]) for s in range(3)) for x in range(2))
        cost=lambda u,v:sum((x-y)**2 for x,y in zip(u,v))
        # Explicit two-row Bayes update, from each full-support first posterior.
        for x in range(2):
            pnext=tuple(sum(eta[x][s]*p[s][y] for s in range(3)) for y in range(2))
            e2=tuple(tuple(eta[x][s]*p[s][y]/pnext[y] for s in range(3)) for y in range(2))
            ini=sum(t*t for t in eta[x])
            after=sum(pnext[y]*sum(t*t for t in e2[y]) for y in range(2))
            rhs=sum(pnext[y]*cost(eta[x],e2[y]) for y in range(2))
            assert after-ini==rhs and (rhs>0)==(len({a,b,c})>1)
            inc+=1
        for m0,m1 in product(range(5),repeat=2):
            M=((F(m0,4),1-F(m0,4)),(F(m1,4),1-F(m1,4)))
            nu=tuple(sum(mu[x]*M[x][y] for x in range(2)) for y in range(2))
            # Maximal coupling from simulated output indices to target mixture.
            L=((min(nu[0],mu[0]),max(0,nu[0]-mu[0])),
               (max(0,nu[1]-mu[1]),min(nu[1],mu[1])))
            assert tuple(sum(r) for r in L)==nu
            assert tuple(sum(L[y][z] for y in range(2)) for z in range(2))==mu
            for psi in permutations(range(3)):
                eta_per=tuple(tuple(eta[y][s] for s in psi) for y in range(2))
                sim=tuple(tuple(sum(p[s][x]*M[x][y] for x in range(2)) for y in range(2)) for s in range(3))
                delta=max(abs(sim[s][0]-p[psi[s]][0]) for s in range(3))
                cost_first=sum(mu[x]*M[x][y]*cost(eta[x],eta_per[y]) for x,y in product(range(2),repeat=2))
                cost_second=sum(L[y][z]*cost(eta_per[y],eta_per[z]) for y,z in product(range(2),repeat=2))
                coupling=sum(mu[x]*M[x][y]*L[y][z]/nu[y]*cost(eta[x],eta_per[z])
                             for x,y,z in product(range(2),repeat=3) if nu[y]>0)
                assert max(cost_first,cost_second)<=2*delta
                assert coupling<=2*(cost_first+cost_second)<=8*delta
                gluing+=1
    return gluing,inc


if __name__=="__main__":
    print("PASS exact short binomial inverses and distinct first pairs:",
          verify_short_unit_inverses(),verify_first_character_pairs())
    print("PASS one-nonzero mixture counts:",verify_mass())
    print("PASS rational posterior gluing and strict-increment cases:",verify_couplings_and_increment())
