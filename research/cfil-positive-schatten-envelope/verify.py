"""Exact endpoint/fixture tests plus separate numerical stress tests (not a proof).
Requires Python 3, NumPy. Run: python verify.py; also safe under python -O.
"""
from fractions import Fraction as F
from itertools import permutations
from math import comb, hypot
import numpy as np
from numpy.linalg import eigh, eigvalsh

def check(test, msg):
    if not test:
        raise RuntimeError(msg)

def exact_checks():
    # Integer noncommuting positive definite matrices (L L^T).
    a=np.array([[2,0,0],[1,1,0],[0,1,3]],dtype=object)
    b=np.array([[1,0,0],[2,3,0],[-1,2,2]],dtype=object)
    a=a@a.T; b=b@b.T
    # Heinävaara degree-four moment from the pencil Taylor coefficients.
    def trword(word):
        x=np.eye(3,dtype=object)
        for i in word:
            x=x@(a if i==0 else b)
        return int(x.trace())
    def shuffle(i,j):
        ws=set(permutations((0,)*i+(1,)*j))
        return F(sum(trword(w) for w in ws),len(ws))
    mixed=shuffle(2,2)
    ordinary=trword((0,0,1,1)); c=a@b-b@a
    c2=int((c.T@c).trace())
    check(ordinary-mixed==F(c2,6)>0,"fourth mixed moment")
    for i in range(1,5):
        check(shuffle(i,1)==trword((0,)*i+(1,)), "derivative on second axis")
        check(shuffle(1,i)==trword((0,)+(1,)*i), "derivative on first axis")
    # Coefficient of s^2 t^2 in the GT difference before radial mixing.
    check(F(ordinary,4)-mixed/F(4)==F(c2,24),"fourth GT coefficient")
    # Use a Pythagorean parameter to avoid radicals in prescribed triples.
    m=0
    for i in range(11):
        h=F(i,10); u=2*h/(1+h*h); d=(1-h*h)/(1+h*h)
        for j in range(13):
            th=F(j,12); s=F(j+1,7)
            a1,a2=s*th*(1+d),s*(1-th)*(1-d)
            b1,b2=s*th*(1-d),s*(1-th)*(1+d)
            check((a1+b1,a2+b2)==(2*s*th,2*s*(1-th)),"sharp diagonal sums")
            check((a1*b1,a2*b2)==((s*th*u)**2,(s*(1-th)*u)**2),"true overlap")
            X,Y=a1+a2,b1+b2
            check(X+Y==2*s and (s*u)**2<=X*Y,"admissible")
            if d: check((1+(X-Y)/(2*s*d))/2==th,"solving for theta")
            m+=1
    return ordinary,mixed,c2,m

def power(A,r):
    x,U=eigh(A); x=np.maximum(x,0.)
    return (U*x**r)@U.conj().T

def norm(A,p):
    return (np.maximum(eigvalsh(A),0.)**p).sum()**(1/p)

def stats(A,B,p):
    Ap=power(A,p/2); Bp=power(B,p/2)
    x=float(np.vdot(Ap,Ap).real); y=float(np.vdot(Bp,Bp).real)
    s=(x+y)/2
    if s==0: return 0,0,0,0
    u=np.clip(np.vdot(Ap,Bp).real/s,0,1)
    d=np.sqrt((1-u)*(1+u))
    # 1-d computed stably even for overlaps near 0.
    lo=u*u/(1+d)
    im=s**(1/p)*((1+d)**(1/p)+lo**(1/p))
    cfil=(2*s)**(1/p)*(1+u**(2/p))**(1-1/p)
    return norm(A+B,p),im,cfil,u

def stress():
    rnd=np.random.default_rng(26261118)
    ps=(2,2.01,2.33,2.5,3,3.8,4,4.99,6.5,7.99,9.33,14,27)
    ntest=0; near=0
    for d in (2,3,4,7):
        for case in range(24):
            def gen(r):
                q,r0=np.linalg.qr(rnd.normal(size=(d,r))+1j*rnd.normal(size=(d,r)))
                v=rnd.uniform(.02,1.,r)
                return (q*v)@q.conj().T
            A=gen(1+case%d)
            if case%8==0: B=A
            elif case%8==1: B=A+1e-7*gen(d)
            elif case%8==2: B=1e-8*gen(d)
            elif case%8==3: B=np.zeros_like(A)
            else: B=gen(1+(3*case+1)%d)
            for p in ps:
                v,i,c,u=stats(A,B,p)
                tol=3e-11*max(1.,i,c)
                check(v<=i+tol and i<=c+tol,("envelope",d,case,p,v,i,c,u))
                if p==2: check(abs(v-i)<tol,"p=2 identity")
                near+=int(abs(v-i)<tol); ntest+=1
    # Explicit sharp commuting unequal-norm family: arbitrary p including noninteger.
    nsh=0
    for th in (.02,.2,.5,.94):
        for u in (0.,.004,.12,.69,.999,1.):
            d=np.sqrt(1-u*u); lo=u*u/(1+d)
            for p in ps:
                a=np.diag(np.asarray([th*(1+d),(1-th)*lo])**(1/p))
                b=np.diag(np.asarray([th*lo,(1-th)*(1+d)])**(1/p))
                v,i,c,uu=stats(a,b,p)
                check(abs(u-uu)<2e-13 and abs(v-i)<1e-12,("sharp",u,th,p))
                nsh+=1
    return ntest,near,nsh

if __name__=="__main__":
    a,m,c,n=exact_checks()
    print(f"EXACT: Tr A²B²={a}; shuffle(2,2)={m}; commutator norm²={c}; {n} sharp triples")
    n,near,s=stress(); print(f"NUMERICAL: {n} matrix/exponent trials ({near} near equality); {s} sharp fixtures")
