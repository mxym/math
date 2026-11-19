#!/usr/bin/env python3
"""Optional exact enclosure of the 1324 density. Decimal Newton guesses are untrusted."""
from decimal import Decimal as D, getcontext
from fractions import Fraction as Q
from math import isqrt
import check
check.S=10**200
from check import I,need
M=90
def proposals():
    """Build real approximations; *any* feasible output is audited below with rational bounds."""
    getcontext().prec=150
    y0=(D(3).sqrt()-1)/2
    xs=[D('.3051')*y0**j for j in range(M+1)]
    for it in range(12):
        E=[];a=[];b=[];c=[]
        for j,x in enumerate(xs):
            sm=xs[j+1] if j<M else y0*x
            u=xs[j-1] if j else 1-x
            e=sm*(x-sm)*(2-3*x+sm)+(1-u)*(u-x)*(u-3*x)
            ds=(x-2*sm)*(2-3*x+sm)+sm*(x-sm)
            du=-(u-x)*(u-3*x)+(1-u)*(2*u-4*x)
            dx=sm*(2-6*x+4*sm)+(1-u)*(6*x-4*u)
            E.append(-e);a.append(du if j else 0);b.append(dx-(du if not j else 0)+(y0*ds if j==M else 0));c.append(ds if j<M else 0)
        for j in range(1,M+1):
            ratio=a[j]/b[j-1]; b[j]-=ratio*c[j-1];E[j]-=ratio*E[j-1]
        for j in range(M,-1,-1):
            E[j]=(E[j]-(c[j]*E[j+1] if j<M else 0))/b[j]
        xs=[x+e for x,e in zip(xs,E)]
    return Q(xs[0]),[Q(v/u) for u,v in zip(xs,xs[1:])]
def inv(a):
    need(a.a>0,'nonpositive denominator');S=check.S
    return I.raw(S*S//a.b,-((-S*S)//a.a))
def symmetric(x):
    m=max(abs(x.a),abs(x.b));return I.raw(-m,m)
def sqerr(x):
    m=max(abs(x.a),abs(x.b));return I.raw(0,-((-m*m)//check.S))
def certify(t0,ratios):
    S=check.S
    need(Q(29,100)<t0<Q(321,1000) and all(check.A<y<check.B for y in ratios),'bad proposals')
    ts=[I(t0)];ys=[I(y) for y in ratios]
    for y in ys: ts.append(ts[-1]*y)
    # sqrt(3) enclosure and exact Price fixed point at zero
    u=isqrt(3*S*S);rt=I.raw(u,u+1)
    y=(rt-1)*Q(1,2);g0=rt*Q(2,3)-1;d0=-y*(1-y)**2*inv(1-y**4)
    t=ts[-1]
    g=g0+t*d0+I(0,Q(1,50))*t**2
    d=d0+I(0,Q(1,25))*t
    for t,y in reversed(list(zip(ts[:-1],ys))):
        f=y**3*g+(1-t)*y*(1-y)**2
        fy=3*y**2*g+t*y**3*d+(1-t)*(1-y)*(1-3*y)
        ft=y**4*d-y*(1-y)**2
        g=f+Q(3,2)*sqerr(fy)
        d=ft+3*symmetric(fy) # |H_ty| < 1 and optimal y differs from trial by at most 3 |H_y|.
    t=ts[0]
    W=2*t**3*g+t*t*(1-2*t)**2
    W1=6*t*t*g+2*t**3*d+2*t*(1-2*t)*(1-4*t)
    return 12*(W+Q(5,4)*sqerr(W1))
if __name__=='__main__':
    v=certify(*proposals()); print('density enclosure, endpoints times 10^200:');print(v.a);print(v.b)
    n=100;place=check.S//(10**n)
    need(v.a//place==v.b//place,'insufficient precision');print('100 certified decimal places (truncated): 0.'+str(v.a//place).zfill(n))
