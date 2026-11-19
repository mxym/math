"""Finite exact consistency checks, not the proof. Python standard library only."""
from fractions import Fraction as F
from math import factorial

def req(v, label):
    if not v:
        raise ArithmeticError(label)

def prod(xs):
    z=F(1)
    for x in xs:
        z*=x
    return z

def dir_moment(d,j):
    return prod(F(2*i+1,d+2*i) for i in range(j))

def moment(k,d,y,projected):
    # Coefficients in u of E|ye1+sqrt(u)Z|^(2k).
    # For projected Z, |Z|^2 ~ Beta(d/2,2) independently of direction.
    out=[F(0)]*(k+1)
    for j in range(k//2+1):
        for h in range(k-2*j+1):
            k0=k-2*j-h
            r=h+j
            coeff=factorial(k)//(factorial(k0)*factorial(2*j)*factorial(h))
            coeff*=y**(2*k0)*(2*y)**(2*j)*dir_moment(d,j)
            if projected:
                coeff*=prod(F(d+2*i,d+4+2*i) for i in range(r))
            out[r]+=coeff
    return out

def main():
    cnt=0
    for d in [3,4,5,6,10,23,128]:
        for k in range(2,11):
            for y in map(F,[0,1,2,F(2,3),F(7,9)]):
                left=moment(k,d,y,False);right=moment(k-2,d,y,True)
                scale= F(2*k*(2*k+d-2)*(2*k-2)*(2*k+d-4),4*d*(d+2))
                req(all((i+2)*(i+1)*left[i+2]==scale*x for i,x in enumerate(right)),(d,k,y))
                cnt+=1
    count=0
    for d in [*range(3,150),320,1009]:
        raw=lambda k: prod(F(d+2*j,d) for j in range(k))
        v=raw(2)-1; fourth=raw(4)-4*raw(3)+6*raw(2)-3
        req(v==F(2,d) and fourth==F(12,d*d)+F(48,d**3),d)
        req(fourth<=F(28,d*d) and v-fourth/16>=F(1,d),d)
        count+=1
    # d=3, p=1: integrate (y^2+r^2+2yrv)^(1/2) with v uniform [-1,1].
    joins=0
    for y in [F(1,5),F(1,3),F(1),F(5,2)]:
        for r in [F(1,7),F(1,3),F(1,2),F(1),F(7,3),y]:
            val=((y+r)**3-abs(y-r)**3)/(6*y*r)
            reg=(y+r*r/(3*y)) if r<=y else r+y*y/(3*r)
            req(val==reg,(y,r))
            if r>y:
                req((y*y-r*r)/(4*r**5)<0,(y,r))
            if r==y:
                req(F(1,3)/y==1/(2*r)-y*y/(6*r**3),y)
            joins+=1
    req(F(1,120)-F(1,2)*F(1,6)**2==-F(1,180),"log sinc")
    print("Exact squared-radius second-derivative polynomial identities:",cnt)
    print("Exact chi-square moment and retained-variance checks:",count)
    print("Exact two-sphere endpoint integrations (incl joins):",joins)
    print("Exact fourth-order logarithmic sinc coefficient: -1/180")
    print("PASS finite consistency only; main and asymptotic results are analytic.")

if __name__=="__main__":
    main()
