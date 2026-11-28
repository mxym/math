#!/usr/bin/env python3
"""Exact finite checks for the pinned-gradient relative-cutoff proof."""
from collections import Counter
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import product
from random import Random


def energy(y, pins, edges):
    return sum(v*x*x for v,x in zip(pins,y))+sum(
           w*(y[i]-y[j])**2 for i,j,w in edges)



def signed_energy(y,pins,edges):
    return sum(p*x*x for p,x in zip(pins,y))+sum(
               w*(y[i]-a*y[j])**2 for i,j,w,a in edges)


def layer(y,h):
    mag=list(map(abs,y))
    t=max(mag)
    assert t>2*len(y)*h
    vals=[t/2]+sorted({x for x in mag if x>t/2})
    pair=max(zip(vals,vals[1:]),key=lambda z:z[1]-z[0])
    assert pair[1]-pair[0]>h
    S=frozenset(i for i,x in enumerate(mag) if x>=pair[1])
    z=tuple((1 if x>0 else -1) if i in S else 0 for i,x in enumerate(y))
    u=tuple(x-h*t for x,t in zip(y,z))
    assert all(abs(u[i])>abs(u[j]) for i in S for j in range(len(y)) if j not in S)
    assert all(u[i]*z[i]>0 for i in S)
    return z,u


def exact_trials():
    rng=Random(2794)
    count=nonlinear=0
    for n in range(1,11):
        for _ in range(90):
            pins=[rng.randrange(0,7)*F(1+rng.randrange(31),9) for i in range(n)]
            pins[0] += 3
            edges=[(i,i+1,F(1+rng.randrange(11)),rng.choice((-1,1))) for i in range(n-1)]
            edges += [(i,j,F(rng.randrange(4),7),rng.choice((-1,1))) for i in range(n)
                      for j in range(i+2,n) if rng.randrange(2)]
            if edges:
                i,j,w,a=edges[0]
                edges[0]=(i,j,w+2**(40+rng.randrange(130)),a)
            h=rng.randrange(1,6)
            y=[F(rng.randrange(-100,101),rng.randrange(1,19)) for i in range(n)]
            y[rng.randrange(n)]+=rng.choice((-1,1))*(3*n*h+101)
            z,u=layer(y,h)
            c=signed_energy(z,pins,edges)
            assert c>0
            assert signed_energy(y,pins,edges)-signed_energy(u,pins,edges)>=c*h*h
            count+=1
            for a,b in ((1,4),(2,1),(4,2)):
                lhs=sum(w*(abs(y[i])**a-abs(u[i])**a)
                        for i,w in enumerate(pins))
                lhs+=sum(w*(abs(y[i]-s*y[j])**b-abs(u[i]-s*u[j])**b)
                         for i,j,w,s in edges)
                rhs=sum(w*abs(h*z[i])**a for i,w in enumerate(pins))+sum(
                        w*abs(h*(z[i]-s*z[j]))**b for i,j,w,s in edges)
                assert lhs>=rhs
                nonlinear+=1
    return count,nonlinear


def fiber_test():
    nrows=0
    peaks=[]
    for n in range(1,5):
        ys=[F(i,10) for i in range(n)]
        images=Counter()
        axis=(-2*n-2,-2*n-1,-n,-1,0,1,n,2*n+1,2*n+2)
        for x in product(axis,repeat=n):
            y=tuple(F(a)-b for a,b in zip(x,ys))
            if max(map(abs,y))<=2*n:
                continue
            z,u=layer(y,1)
            images[u]+=1
            nrows+=1
        peaks.append(max(images.values()))
        assert peaks[-1]<=n
    # The map is not generally injective, even in two unshifted coordinates.
    assert layer((F(5),F(7)),1)[1] == layer((F(6),F(7)),1)[1] == (5,6)
    return nrows+2,peaks


def negacyclic():
    nrows=0
    for n in range(3,10):
        w=2**(3*n)+F(1,3)
        edges=[(j,j+1,w,1) for j in range(n-1)]+[(0,n-1,w,-1)]
        V=set()
        for z in product((-1,0,1),repeat=n):
            if any(z):
                e=signed_energy(z,[0]*n,edges)
                direct=w*(sum((z[j]-z[j-1])**2 for j in range(1,n))+
                          (z[0]+z[-1])**2)
                assert direct==e
                V.add(e)
                nrows+=1
        assert min(V)==2*w
    return nrows


def linear_solve(Q,h):
    a=[list(map(F,row))+[F(v)] for row,v in zip(Q,h)]
    n=len(a)
    for k in range(n):
        s=next(i for i in range(k,n) if a[i][k])
        a[s],a[k]=a[k],a[s]
        w=a[k][k]
        a[k]=[v/w for v in a[k]]
        for i in range(n):
            if i==k:
                continue
            w=a[i][k]
            a[i]=[v-w*u for v,u in zip(a[i],a[k])]
    return tuple(row[-1] for row in a)


def embedding():
    rng=Random(39267)
    core=clip=0
    for n in range(1,5):
        for _ in range(25):
            fields=[F(rng.randrange(-40,41),11) for i in range(n)]
            beta=5+4*max(map(abs,fields))
            pins=[beta]*n
            J=[(i,j,F(rng.randrange(0,20),3)) for i in range(n)
               for j in range(i+1,n) if rng.randrange(2)]
            E=[(i,j,2*v) for i,j,v in J]
            Q=[[beta*(i==j) for j in range(n)] for i in range(n)]
            for i,j,w in E:
                Q[i][j]-=w
                Q[j][i]-=w
                Q[i][i]+=w
                Q[j][j]+=w
            b=linear_solve(Q,fields)
            t=[F(1,2)+v for v in b]
            assert all(F(1,4)<=v<=F(3,4) for v in t)
            const=sum(Q[i][i] for i in range(n))/4+sum(v*h for v,h in zip(b,fields))
            for x in product((0,1),repeat=n):
                s=[2*v-1 for v in x]
                v=const-sum(w*s[i]*s[j] for i,j,w in J)-sum(h*k for h,k in zip(fields,s))
                assert v==energy([a-c for a,c in zip(x,t)],pins,E)
                core+=1
            for x in product(range(-1,3),repeat=n):
                u=[min(1,max(0,v)) for v in x]
                y=[a-c for a,c in zip(x,t)]
                yy=[a-c for a,c in zip(u,t)]
                assert all((y[i]-y[j])**2 >= (yy[i]-yy[j])**2 for i,j,w in E)
                assert energy(y,pins,E)-energy(yy,pins,E)>=beta*sum(
                       (v-k)**2 for v,k in zip(x,u))
                clip+=1
    return core,clip


def as_decimal(x):
    x=F(x)
    return D(x.numerator)/D(x.denominator)


def lse(v):
    a=max(v)
    return a+sum((x-a).exp() for x in v if x-a > -500).ln()


def stiff_elimination():
    rng=Random(5042)
    blocks=0
    with localcontext() as ctx:
        ctx.prec=175
        for n in range(1,5):
            for _ in range(15):
                pins=[F(1+rng.randrange(11),3) for i in range(n)]
                pins[0]+=2**(280+rng.randrange(41))
                edges=[(i,i+1,2**(250+rng.randrange(30))+F(rng.randrange(6),5),rng.choice((-1,1)))
                        for i in range(n-1)]
                frac=[F(rng.randrange(9),9) for i in range(n)]
                cols=[[F(i)-a for i in range(-1,3)] for a in frac]
                direct=lse([-as_decimal(signed_energy(y,pins,edges))
                            for y in product(*cols)])
                prev=[-as_decimal(pins[0]*x*x) for x in cols[0]]
                for i,j,w,sign in edges:
                    prev=[-as_decimal(pins[j]*y*y)+lse([
                        v-as_decimal(w*(y-sign*x)**2) for v,x in zip(prev,cols[i])])
                        for y in cols[j]]
                dp=lse(prev)
                assert abs(dp-direct)<D("1e-70")
                blocks+=1
    return blocks


if __name__=="__main__":
    print("PASS: cut layers/mixed potentials/fibers/embedding/clipping/stiff tables/twisted cycles")
    print(*exact_trials(),*fiber_test(),*embedding(),stiff_elimination(),negacyclic())
