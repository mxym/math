"""Exact finite tests for the parity-crossover proof, not evidence of a uniform limit."""
from fractions import Fraction as F
from math import prod, comb, factorial, pi, sqrt, exp, sinh, cosh, log
from itertools import product
def ck(test,msg):
    if not test: raise ArithmeticError(msg)
def det(x):
    t=[r[:] for r in x]; v=1
    for i in range(len(t)):
        a=next((k for k in range(i,len(t)) if t[k][i]),None)
        if a is None:return 0
        if a!=i:t[a],t[i]=t[i],t[a];v=-v
        z=t[i][i];v*=z
        for k in range(i+1,len(t)):
            f=t[k][i]/z
            t[k]=[a-f*b for a,b in zip(t[k],t[i])]
    return v
def bern(q,x):return prod(t if b else 1-t for t,b in zip(q,x))
def tests(q,z):
    m=len(q);ck(sum(q)==F(m,2),'test slice')
    # z=e^s, uncentered denominator for odds scale z^2; no irrational powers.
    h=[1+(z*z-1)*t for t in q]
    a=[t*z*z/b for t,b in zip(q,h)]
    k=[b/z for b in h]
    V=sum(t*(1-t) for t in q)
    jac=[]
    for i,(b,p) in enumerate(zip(h,a)):
        row=[z*z/b**2*(int(i==j)-int(i==m-1)) for j in range(m-1)]
        jac.append(row+[2*p*(1-p)])
    ck(abs(det(jac))==2*V/prod(k)**2,'Jacobian')
    b=F(0); B=F(0)
    for v in product((0,1),repeat=m):
        r=sum(v); a1=bern(a,v); a2=bern(q,v)
        ck(a1*prod(k)==a2*z**(2*r-m),'full likelihood ratio')
        if 2*r<=m:b+=a1;B+=a2*z**(2*r-m)
    ck(B==b*prod(k),'strict win complement, including even ties')
    return 2**m
def main():
    jobs=0; states=0
    for m in range(2,10):
        for delta in (F(1,7),F(2,9)):
            q=[F(1,2)] if m%2 else []
            for j in range(m//2):
                t=delta/F(j+1);q.extend((t,1-t))
            for z in (F(5,4),F(2),F(7,2)):
                jobs+=1;states+=tests(q,z)
    print(f'Exact odds shift, full Jacobian, strict tail: {jobs} cases, {states} joint Bernoulli atoms.')
    # Check the centered slice density by exact Irwin-Hall inclusion/exclusion.
    for m in (25,50,100,200):
        x=F(m,2)
        dm=sum((-1)**j*comb(m,j)*(x-j)**(m-1) for j in range(m//2+1))/factorial(m-1)
        ck(abs(float(dm)/sqrt(6/(pi*m))-1)<1/m,'slice Gaussian scale')
    # For a fixed legal q environment q_i=1/2 the exact tilted weighted tail
    # has a different V/m, but precisely the same parity/geometric multiplier.
    for m in (600,601):
        for a in (0.5,1,2):
            exact=sum(exp(-a*(m-2*k))*float(F(comb(m,k),2**m)) for k in range(m//2+1))*sqrt(m)
            lim=sqrt(2/pi)*exp(-a*(m%2))/(1-exp(-2*a))
            ck(abs(exact/lim-1)<0.014,'parity CDF factor')
    print('Exact central slice at m=25,50,100,200; binomial geometric factor on both parities at three tilts.')
    print('PASS')
if __name__=='__main__':main()
