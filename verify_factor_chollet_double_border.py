#!/usr/bin/env python3
"""Exact interval proof for the order-eleven Chollet double-border schedule."""
from fractions import Fraction as F

if not __debug__:
    raise RuntimeError("run without -O")

# r, t_plus, t_minus, mu. Adjacent rows are joined linearly.
SCHEDULE=tuple(tuple(F(str(x)) for x in row) for row in (
    ("0.417","1.48133","1.14730","1.170487"),
    ("0.427","1.48627","1.14456","1.174417"),
    ("0.447","1.49619","1.13919","1.182590"),
    ("0.477","1.51138","1.13124","1.195609"),
    ("0.507","1.52572","1.12400","1.210275"),
    ("0.557","1.54394","1.11480","1.244647"),
    ("0.607","1.54975","1.10900","1.284309"),
    ("0.657","1.55322","1.08219","1.338245"),
    ("0.707","1.55674","1.06407","1.388635"),
    ("0.757","1.55941","1.04920","1.443152"),
    ("0.807","1.56011","1.03000","1.515470"),
    ("0.857","1.56184","1.01969","1.577454"),
    ("0.907","1.56216","1.00967","1.651524"),
    ("0.957","1.56242","1.00332","1.721998"),
    ("1","1.56120","1.00021","1.779121"),
))


def weight(r,t1,t2):
    # Weighted average of t1^2 and t2^2; increasing in r if t1>=t2.
    c,s=(1+r)/2,(1-r)/2
    a,b=c*c*(t2*t2-1),s*s*(t1*t1-1)
    assert a+b>0
    return (a*t1*t1+b*t2*t2)/(a+b)


def check(lo,hi,parlo,parhi,deg=9):
    t1,t2,mu=[min(a,b) for a,b in zip(parlo,parhi)]
    T1,T2,MU=[max(a,b) for a,b in zip(parlo,parhi)]
    assert t1>T2>=t2>1 and mu>0
    w1=weight(lo,t1,t2); w2=t1*t2
    ca,cb=(1+lo)/2,(1+hi)/2
    sa,sb=(1-hi)/2,(1-lo)/2
    Ca,Cb=(1+lo*lo)/2,(1+hi*hi)/2
    Sa,Sb=(1-hi*hi)/2,(1-lo*lo)/2
    c0,c1,s0,s1=ca*ca,cb*cb,sa*sa,sb*sb
    C1,S1=Cb*Cb,Sb*Sb
    assert all(a>=0 for a in (c0,c1,s0,s1,C1,S1))
    minimum=None
    for k in range(deg+1):
        for parity in range(2):
            lower=upper=None
            for a in range(parity,k+1,2):
                b=k-a
                aa,bb=(a+2)*(a+1),(b+2)*(b+1)
                p=c0*aa+s0*bb-MU*T1**a*T2**b
                q=mu*mu*w1**a*w2**b-C1*aa-S1*bb
                if lower is not None:
                    prod=a*(a-1)*(b+2)*(b+1)
                    p-=c1*s1*prod/lower
                    q-=C1*S1*prod/upper
                if min(p,q)<=0: return None
                minimum=min(p,q) if minimum is None else min(minimum,p,q)
                lower,upper=p,q
    return minimum


# The two polynomials for each of 7 and 9 and the multipliers are from
# McBee's public order-ten proof. We only need r>=1/5 for 7 and r>=8/25 for 9.
PRIOR=(
    (7,F(1,5),((F(71,50),F(4,5),-F(9,20)),
                 (F(71,50),-F(3,5),F(11,50)),(F(1),F(0),F(1,2)))),
    (9,F(8,25),((F(34,25),F(29,50),-F(13,50)),
                  (F(34,25),-F(14,25),F(11,50)),(F(103,100),F(0),F(11,20)))),
)


def polynomial_bounds(p,l,r):
    a,b,c=p
    xs=[l,r]
    if c and l<-b/(2*c)<r: xs.append(-b/(2*c))
    values=[a+x*(b+x*c) for x in xs]
    return min(values),max(values)


def prior_replay():
    for k in range(6):
        assert (k+1)<=2**k<=(k+1)**2
    for n,l,polys in PRIOR:
        def go(l,r,d):
            assert d<=20
            pr=tuple(zip(*(polynomial_bounds(p,l,r) for p in polys)))
            if check(l,r,*pr,deg=n-2) is not None: return 1,d
            m=(l+r)/2
            a,b=go(l,m,d+1)
            c,e=go(m,r,d+1)
            return a+c,max(b,e)
        print("PRIOR LADDER PASS",n,l,*go(l,F(1),0),flush=True)


def replay():
    assert SCHEDULE[0][0]==F(417,1000) and SCHEDULE[-1][0]==1
    total=0
    maxdepth=0
    margin=None
    stats=[]
    for (l,*a),(r,*b) in zip(SCHEDULE,SCHEDULE[1:]):
        assert 0<l<r<=1
        covered=0
        def verify(lo,hi,plo,phi,depth):
            nonlocal covered,maxdepth,margin
            z=check(lo,hi,plo,phi)
            if z is not None:
                covered+=1;maxdepth=max(maxdepth,depth)
                u=z*10**9//1
                margin=u if margin is None else min(margin,u)
                return
            if depth>=24:raise AssertionError(("unclosed parameter chart",lo,hi))
            mid=(lo+hi)/2
            pp=tuple((x+y)/2 for x,y in zip(plo,phi))
            verify(lo,mid,plo,pp,depth+1)
            verify(mid,hi,pp,phi,depth+1)
        verify(l,r,a,b,0)
        stats.append(covered)
        total+=covered
    assert check(F(1),F(1),SCHEDULE[-1][1:],SCHEDULE[-1][1:])>0
    print("BORDER PASS: order 11",total,maxdepth,margin,stats,flush=True)
    return total,maxdepth,margin,stats

if __name__=="__main__":
    prior_replay()
    replay()
