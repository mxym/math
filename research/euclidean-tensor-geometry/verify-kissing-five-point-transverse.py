#!/usr/bin/env python3
"""Exact arithmetic controls for five-point transverse stability. No numerical eigensolver."""
from fractions import Fraction as F
from itertools import product
def proj(t):return ((1-t*t)/(1+t*t),2*t/(1+t*t))
def inner(x,y):return sum(a*b for a,b in zip(x,y))
def phase(z,k):
    a,b=F(1),F(0)
    for _ in range(k):a,b=a*z[0]-b*z[1],a*z[1]+b*z[0]
    return a,b
def solve(M):
    n=len(M)
    for j in range(n):
        i=next(i for i in range(j,n) if M[i][j]);M[i],M[j]=M[j],M[i]
        s=M[j][j];M[j]=[v/s for v in M[j]]
        for i in range(n):
            if i!=j:
                s=M[i][j];M[i]=[a-s*b for a,b in zip(M[i],M[j])]
    return [a[-1] for a in M]
def test(Y):
    w=solve([[F(1)]*5+[F(1)]]+[[phase(z,k)[j] for z in Y]+[F(0)] for k in (2,4) for j in (0,1)])
    assert min(w)>0 and sum(w)==1
    cos=lambda i,j:inner(Y[i],Y[j]);f=lambda u:u**4-u**2/4;df=lambda u:4*u**3-u/2
    def norm(a):return sum(v*x*x for v,x in zip(w,a))
    def harmonic(a,k):
        return sum(sum(wi*x*phase(z,k)[j] for wi,x,z in zip(w,a,Y))**2 for j in (0,1))
    for rep in range(1,25):
        # Rational elevations and positive radial factors with r_i^2+h_i^2=1.
        t=[F(((rep*(j+2)**2+3*j)%23)-11,480) for j in range(5)]
        h=[2*x/(1+x*x) for x in t];r=[(1-x*x)/(1+x*x)for x in t]
        d2=max(x*x for x in h);V=norm(h);Vperp=V-2*harmonic(h,1)
        quad=F(0);energy=F(0)
        for i,j in product(range(5),repeat=2):
            c=cos(i,j);G=r[i]*r[j]*c+h[i]*h[j]
            quad+=w[i]*w[j]*df(c)*(h[i]*h[j]-c*(h[i]**2+h[j]**2)/2)
            energy+=w[i]*w[j]*f(G)
        assert quad==harmonic(h,3)-F(5,4)*Vperp
        assert quad<=-Vperp/4 and d2<=F(1,256)
        assert abs(energy-F(1,4)-quad)<=25*d2*V
    return 24
def main():
    eps2=F(1,256);g=1/(8*(1-eps2))
    assert 7*g+23*(1+g*eps2)**2<25 and F(1,4)-25*eps2>=F(1,8)
    n=sum(test([proj(t) for t in ts]) for ts in [
        list(map(F,('0','3/4','3','-3','-3/4'))),list(map(F,('0','7/10','31/10','-29/10','-3/4')))])
    # At the six signed ends of three regular axes, give alternating elevations.
    # The absolute off-axis product becomes 1/2-3u/2, u=h^2.
    # Compute coefficients of (2/3)f(1/2-3u/2), i.e. energy minus 1/4.
    def prod(a,b):
        z=[F(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):z[i+j]+=x*y
        return z
    v=[F(1,2),F(-3,2)];sq=prod(v,v);four=prod(sq,sq)
    co=[F(2,3)*(z-(sq[j]/4 if j<len(sq) else 0)) for j,z in enumerate(four)]
    assert co[0]==0 and co[1]==-F(1,4)
    print('PASS:',n,'rational lifted configurations; sharp six-end defect',*[str(x)for x in co])
if __name__=='__main__':main()
