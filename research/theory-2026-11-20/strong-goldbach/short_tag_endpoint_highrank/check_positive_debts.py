#!/usr/bin/env python3
"""Exact coefficient and rail replay; no analytic distribution is checked."""
from fractions import Fraction as F
from itertools import combinations
from random import Random


def ck(ok, label):
    if not ok:
        raise ArithmeticError(label)


def subs(n):
    a=n
    while 1:
        yield a
        if not a:
            return
        a=(a-1)&n


def positive_cases(es, eta, kappa):
    vals=[sum(e for i,e in enumerate(es) if m>>i&1) for m in range(1<<len(es))]
    full=(1<<len(es))-1
    got=[0,0,0]
    for s in range(1,full+1):
        r=full^s
        if vals[r]<=50030:
            continue
        T0=min(153200-vals[s],183600-2*vals[s],101000)
        T=max(100060,T0)
        K=(-1)**r.bit_count()
        ff=-sum((-2)**(r^a).bit_count() for a in subs(r) if 2*vals[a]>T)
        G=0
        for a in subs(r):
            v=r^a
            if min(vals[a],vals[v])<eta or 2*max(vals[a],vals[v])>T:
                continue
            for c in subs(v):
                if vals[c]<=kappa and v!=c:
                    G+=(-3)**c.bit_count()
        H=K-ff-G
        if max(es)>50500:
            ck(H==0,("giant case",es,r,H))
        if H<=0:
            continue
        ck(H<=2,("debt coefficient",es,r,H))
        rs=sorted(es[i] for i in range(len(es)) if r>>i&1)
        if len(rs)==2:
            p,P=rs
            ck(p<eta and 50030-p<P<=50030,("true nonlog tiny pair",es,r,H))
            ck(s.bit_count() in (1,2),("source-rank count",es,r,H))
            got[s.bit_count()-1]+=1
        else:
            ck(len(rs)==3 and s.bit_count()==1,("r3 correction",es,r,H))
            p,q,t=rs
            ck(p<=kappa and q>kappa and q>=eta-kappa and 50030-p<q+t<=50030,
                ("tiny correction r3",es,r,H))
            got[2]+=1
    return got


def run():
    # Numbers here are normalized log labels, not mock asserted primes.
    eta,kappa=80,20
    rng=Random(7083)
    examples=[(50,50000,49950),(50,50000,24975,24975),(10,25005,25020,49965)]
    n=0
    all_got=[0,0,0]
    for rank in [3,4]:
        for _ in range(2000):
            ep=rng.randrange(1,eta)
            if _%4==0:
                w=50030-rng.randrange(ep)
                x=100000-ep-w
                if rank==3:
                    examples.append((ep,w,x))
                else:
                    z=rng.randrange(1,x)
                    examples.append((ep,w,z,x-z))
            elif _%4==1 and rank==4:
                ep=rng.randrange(1,kappa+1)
                w=50030-rng.randrange(ep)
                z=rng.randrange(1,w)
                examples.append((ep,z,w-z,100000-ep-w))
            else:
                pts=[0]+sorted(rng.sample(range(1,100000-ep),rank-2))+[100000-ep]
                examples.append((ep,)+tuple(b-a for a,b in zip(pts,pts[1:])))
    for ex in examples:
        n+=1
        vv=positive_cases(ex,eta,kappa)
        all_got=[a+b for a,b in zip(all_got,vv)]
    ck(all(all_got),all_got)
    ck(F(".918")-F(".5003")==F(".4177"),"literal lift start")
    ck(F(".082")+F(3,2)*F(".504")<1,"two-free endpoint reserve")
    ck(F(".7545")+F(".02")+F(".002")+F(".0001")<1,"two-sieve summed primary error")
    ck(F(".501")+F(".02")+F(".002")+2*F(".0001")<1,"two-sieve summed full-period error")
    # ell powers alone: eta/2 dominates rough alias, kappa ell^2 dominates ell,
    # and kappa/eta^2 decays, while eta log ell also tends to zero.
    ep=F(1,4); cp=F(3,4)
    ck(ep<cp<1 and cp>2*ep and 2-cp>1,"growing cutoffs")
    print(f"{n} profiles; positive debt labels {all_got}; exact rails passed")


if __name__=="__main__":
    run()
