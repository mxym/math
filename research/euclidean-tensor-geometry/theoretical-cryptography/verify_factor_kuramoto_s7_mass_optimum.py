
"""Exact rational interval certificate for the S7 generalized mass ratio bound."""
from fractions import Fraction as F
from math import isqrt
from random import Random

class I:
    def __init__(self,l,u=None):
        self.l=F(l);self.u=F(l if u is None else u)
        if self.l>self.u: raise ValueError("reversed interval")
    def __add__(x,y):
        y=mk(y)
        return I(x.l+y.l,x.u+y.u)
    __radd__=__add__
    def __neg__(x): return I(-x.u,-x.l)
    def __sub__(x,y): return x+-mk(y)
    def __rsub__(x,y): return mk(y)+-x
    def __mul__(x,y):
        y=mk(y)
        v=(x.l*y.l,x.l*y.u,x.u*y.l,x.u*y.u)
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(x,y):
        y=mk(y)
        if y.l<=0<=y.u: raise ZeroDivisionError("interval contains zero")
        return x*I(1/y.u,1/y.l)
    def sq(x):
        v=(x.l*x.l,x.u*x.u)
        return I(0 if x.l<=0<=x.u else min(v),max(v))
    def sqrt(x):
        if x.l<0: raise ValueError("not a positive interval")
        scale=1<<44
        def root(y): return isqrt((y.numerator*scale**2)//y.denominator)
        return I(F(root(x.l),scale),F(root(x.u)+1,scale))
def mk(y): return y if isinstance(y,I) else I(y)

def q0_sign(q):
    P=1+q
    w=(1+4*q/P.sq()).sqrt()
    f=4*(1-q.sq())*w-2*q.sq()*w.sq()+1-2*q-3*q.sq()
    return f

def chart(Q,m):
    p,l=1+Q,1-Q
    C=2-l.sq()
    D=2*p-4*m
    if D.l<=0 or (4*m-2).l<=0:
        return False
    rr=[(m*(3+Q)-2)/D,(2*p-m*(3+Q))/(4*m-2)]
    der=[(4-4*m-4*m.sq())/D.sq(), (2-m)/(4*m-2)]
    if any(r.l<=0 for r in rr):
        return False
    # All r between the endpoints satisfy B(6/5)<0 and A'(w)<0
    # for w>=6/5. For q<q*, the bracket need not be ordered;
    # the results are then used only on each endpoint as a function.
    z0=F(6,5)
    if (4*rr[1].sq()+C*z0*z0+4*l*p*z0-4*p.sq()).u>=0:
        return False
    if (2*rr[0].sq()*p*(p*z0-l)-C*z0).l<=0:
        return False
    for r,r1 in zip(rr,der):
        R=r.sq()
        R1=2*r*r1
        argument=(l*p).sq()+C*(p.sq()-R)
        if argument.l<=0: return False
        w=2*(argument.sqrt()-l*p)/C
        w1=(8*p+8*Q*w-2*l*w.sq()-4*R1)/(2*C*w+4*l*p)
        z=p*w-l
        J=8*p+8*Q*w-4*l*p*w1-2*R1*z.sq()-4*R*z*(p*w1+w+1)
        if J.u>=0: return False
    return True


def polynomial_checks():
    rng=Random(48073)
    count=0
    def add(x,y):
        m=max(len(x),len(y))
        return [(x[i] if i<len(x) else 0)+(y[i] if i<len(y) else 0)
                for i in range(m)]
    def mul(x,y):
        a=[0]*(len(x)+len(y)-1)
        for i,c in enumerate(x):
            for j,d in enumerate(y): a[i+j]+=c*d
        return a
    def diff(x): return [i*x[i] for i in range(1,len(x))]
    for _ in range(2000):
        q,w,R,u=[F(rng.randrange(0,d+1),d) for d in (991,163,407,641)]
        w*=4;R*=9;u*=7
        p,l=1+q,1-q
        C=2-l*l
        al=l*w-p
        be=l-p*w
        c=4*R+2*w*w
        def Q(v):
            a,b,d=v
            e=-a-b-d
            return u*(a*a+b*b)+(c-u)*(d*d+e*e)-(al*a-p*e)**2-R*be**2*(a+b)**2-(al*b-p*d)**2
        basis=[(1,0,-1),(0,1,0),(1,0,1)]
        M=[[ (Q(tuple(x+y for x,y in zip(a,b)))-Q(a)-Q(b))/2
             for b in basis] for a in basis]
        f=c-al*al-R*be*be-p*p
        e=-2*al*p-R*be*be
        U0=(c+al*(al+2*p)+R*be*be-p*p)/2
        b33=lambda h: 5*c-4*h-(al+2*p)**2-R*be*be-p*p
        assert M[0][0]==M[1][1]==f and M[0][1]==e
        assert M[0][2]==2*(u-U0)
        assert M[1][2]==f+e-M[0][2] and M[2][2]==b33(u)
        assert f-e==4*R+C*w*w+4*l*p*w-4*p*p
        assert f+e==4*R+C*w*w-2*R*(p*w-l)**2
        assert b33(U0)-2*e-f==8*R+2*C*w*w
        L=[p*p,-l*p,-C/4]
        P=add([0,0,C],mul([2*t for t in L],[2-l*l,2*p*l,-p*p]))
        J=add(mul(diff(diff(P)),diff(L)),[-v for v in mul(diff(P),diff(diff(L)))])
        assert J==[2*l*p*(3*l*l*p*p+l*l+2*p**4+2*p*p-2),
                   -6*l*l*p*p*(l*l+2*p*p-2),
                   -F(3,2)*l*p*C*(6*p*p-C),-2*p*p*C*C]
        count+=1
    print("PASS exact spectral and convexity identities",count)

def main():
    polynomial_checks()
    qlo=F(65056916,10**8); qhi=F(65056918,10**8)
    assert q0_sign(I(qlo)).l>0 and q0_sign(I(qhi)).u<0
    m=I(F(6929077,10**7),F(6929078,10**7))
    def mu(q): return (4+2*q)/(7+q)
    assert m.l<mu(qlo)<mu(qhi)<m.u
    def check_j_bound(z):return 4*z*z-F(391,20)*z+F(123,32)
    assert check_j_bound(F(27,10))<0 and check_j_bound(4)<0
    left,right=F(13,20),F(1)
    stack=[(left,right,0)]
    cells=deep=0
    while stack:
        a,b,j=stack.pop()
        if chart(I(a,b),m):
            cells+=1;deep=max(deep,j)
        else:
            assert j<20,(a,b,"unresolved interval")
            c=(a+b)/2
            stack.extend(((a,c,j+1),(c,b,j+1)))
    print("PASS exact dyadic derivative cover",cells,"leaves; depth",deep)

if __name__=="__main__":
    if not __debug__: raise RuntimeError("run normal Python, not -O")
    main()
