"""Rational inner-square integration. No floating comparison determines a claim."""
from fractions import Fraction as F
from pathlib import Path
def c(test,why):
    if not test:raise ValueError(why)
def box(D=2000):
    E=10**12; si=sj=h=0
    for i in range(D//50,49*D//100):
        for j in range(D//50,49*D//100):
            k=D-i-j
            if k-2<D//50 or k>49*D//100:continue
            den=6*(i+1)*(j+1)*k # cube of reciprocal after integration: D/(6*...)
            ma=((i+1)**2+(j+1)**2+k*k)
            # lower for sum 8 x(1-x)-4v via sum x=1 and v<=1e-10
            cn=8*(D*D-ma)*10**10-12*D*D
            c(cn>0,(i,j))
            si+=E*D//den
            sj+=E*cn//(den*D*10**10)
            h+=1
    z=F(si,E);a=F(sj,E)
    c(4*z*a>F(83,10),'triple x triple')
    c(2*a>F(32,5),'prime x triple')
    print('grid:',D,'subrectangles:',h,'Z lower:',z,'A lower:',a,
          '4ZA lower:',float(4*z*a),'2A lower:',float(2*a))
def locals():
    cnt=0
    for p in [2,3,5,7,11,13]:
        for N in (24,30,50,84,210):
            for s,t in [(F(1),F(1)),(F(2,7),F(3,5)),(F(0),F(5,4))]:
                sm=F(0)
                for n in range(p*p):
                    if n*(N-n)%(p*p)==0:continue
                    sm+=(1-s if n%p==0 else 1)*(1-t if (N-n)%p==0 else 1)
                expect=1-F(1,p) if N%p==0 else 1-F(2,p*p)-(F(1,p)-F(1,p*p))*(s+t)
                c(sm/p**2==expect,(N,p,s,t,sm,expect));cnt+=1
    print('two-variable Euler controls:',cnt)
if __name__=='__main__':box();locals()
