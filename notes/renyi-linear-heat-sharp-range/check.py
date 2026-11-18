#!/usr/bin/env python3
"""Exact checks of auxiliary radial integrals. Not a substitute for the smoothing argument."""
from fractions import Fraction as F
from itertools import product

def require(result,msg):
    if not result: raise RuntimeError(msg)

def constants(d,lam,alpha):
    require(isinstance(d,int) and d>4 and lam>0 and alpha>0,"invalid parameters")
    k=lam*d/2
    require(k>2,"nonintegrable fourth-order terms")
    return k,k-F(d,2)

def escort(d,lam,alpha):
    k,m=constants(d,lam,alpha)
    j=m*(m+d-2); h=m*m
    def v(x,y): return k-(x+y)/(k-1)+x*y/((k-1)**2*(k-2))
    b=k-2*m+h/(k-1)
    return (alpha*d/2)*(v(j,j)+(2/alpha-1)*v(j,h))/(b*b)

def raw(d,lam,alpha):
    # Reconstruct Z' and Z'' directly from ∆ applied twice to
    # f=z^(m/alpha) exp(-z/alpha), without using A,B or their covariance.
    k,m=constants(d,lam,alpha)
    def E(p):
        val=0
        for i,c in p.items():
            moment=F(1)
            if i>=0:
                for j in range(i): moment*=k+j
            else:
                for j in range(1,-i+1): moment/=k-j
            val+=c*moment
        return val
    def lap(p):
        out={}
        for i,c in p.items():
            x=i+m/alpha
            for j,y in ((i-1,4*x*(x-1+F(d,2))),
                        (i,-4*(2*x+F(d,2))/alpha),
                        (i+1,4/alpha**2)):
                out[j]=out.get(j,F(0))+c*y
        return out
    def sq(p):
        out={}
        for i,a in p.items():
            for j,b in p.items(): out[i+j]=out.get(i+j,F(0))+a*b
        return out
    if alpha==1:
        # Independent Bochner computation for Shannon log f = 2m log r - r².
        hp=E({1:4,0:-8*m,-1:4*m*m})
        hpp=-2*(E(sq({0:-2,-1:-2*m}))+(d-1)*E(sq({0:-2,-1:2*m})))
    else:
        p=lap({0:F(1)})
        z1=alpha*E(p)
        z2=alpha*(E(lap(p))+(alpha-1)*E(sq(p)))
        hp=z1/(1-alpha); hpp=(z2-z1**2)/(1-alpha)
    require(hp>0,"nonpositive derivative")
    return -d*hpp/hp**2

def main():
    samples=0
    for d,lam,alpha in product((6,8,11,24,101,202,1001,10000),
            map(F,('1/10','1/4','1/2','1','7/3','4','10','80')),
            map(F,('1/10','2/3','99/100','1','6/5','3/2','2','21/10','3','5'))):
        if lam*d<=4:continue
        x=escort(d,lam,alpha)
        require(x==raw(d,lam,alpha),'direct/escort disagreement')
        if lam==1:require(x==2,'Gaussian criterion')
        samples+=1
    require(samples>500,'insufficient checks')
    print('exact direct/escort cross-checks:',samples)
    for alpha,lam,d,beta in [
            (F('1/2'),F('1/5'),300,F(0)),
            (F(3),F(5),300,F(0)),
            (F(2),F(16),10000,F('1/2')),
            (F('3/2'),F(8),10000,F('5/4')),
            (F(1),F(1),6,F('201/100'))]:
        t=raw(d,lam,alpha)
        require(t<beta,'non-strict certificate')
        print('alpha,lambda,d,test boundary,T:',alpha,lam,d,beta,t)
    try:raw(6,F('2/3'),F('1/2'))
    except RuntimeError:pass
    else: raise RuntimeError('negative-integrability control accepted')
if __name__=='__main__': main()
