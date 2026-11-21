"""Exact power rails, determinant injectivity and cusp-zero / CRT phase checks."""
from fractions import Fraction as F
from itertools import product
from math import gcd

def need(v,x):
    if not v:
        raise RuntimeError(x)

z=F(".0002")
vartheta=F(7,64)
M=[F(0)]*4
for a,b,s,d,e,g in product((F(".425"),F(".451")),(F(".522"),F(".5455")),
            (F(".100"),F(".140")),(F(0),F(".001")),(F(0),F(".001")),
            (F(0),F(".0001"))):
    t=s+a+b+d+e+g-1+z
    q=2*s+d+2*e
    need(t>=F(".047") and t<s and s+t-q+e<F("-.003"),
         "positive frequency scale and determinant support inside level")
    need((b+e-a+z)+e-q<F("-.07"),"completion index inside level")
    base=1-s-a-b-g+(a+b)/2
    diag=base+(a+b+s+t)/2
    ss=base+(s+2*t+3*b/2+e)/2
    zero=base+(a+2*s+2*t)/2
    spec=base+(2*s+b+q/2+vartheta+t+2*e+vartheta*(s-t)+F(".0003"))/2
    need(spec==F(".5")+s+b/2+3*d/4+2*e-g/2+z/2
        +vartheta*(1+s-t)/2+F(".00015"),"full spectral exponent")
    M=list(map(max,zip(M,(diag,ss,zero,spec))))
need(M[0]==F(".99935") and M[1]==F(".980075") and M[2]==F(".86595")
     and M[3]<F(".974"),"all combined exponents")
need(max(M)<1,"strict power saving")

phase_cases=0
for s,sp in product((11,13,17),repeat=2):
    if s==sp:
        continue
    DD={}
    for k,kp in product((-4,-3,-2,-1,1,2,3,4),repeat=2):
        h=k*sp-kp*s
        need(h and h not in DD,"injective determinants")
        DD[h]=1
    for d,e,r in product((3,5),(2,7),(19,23,29,31,37)):
        Q=e*e*d*s*sp
        for inv in range(1,r):
            if gcd(inv,r)>1:
                continue
            w=-(pow(Q,-1,r)*pow(inv,-1,r)%r)
            u=(1+inv*Q*w)//r
            need(u*r-inv*Q*w==1,"actual cusp-zero determinant")
            for ell,nn in ((-3,13),(1,7),(2,-5),(4,27)):
                # CRT r-part and scalar substitution in the Kloosterman unit.
                z1=(ell*pow(e,-1,r)*inv +
                    nn*pow(e*d*s*sp,-1,r)*pow(inv,-1,r))%r
                v=(inv*pow(e,-1,r))%r
                z2=(ell*v+nn*pow(Q,-1,r)*pow(v,-1,r))%r
                need(z1==z2,"CRT residue factor")
                # Exchange variables using symmetry and scaling; the matrix
                # then yields the classical phase with large index at infinity.
                v2=(pow(Q,-1,r)*pow(v,-1,r))%r
                w2=(-pow(Q,-1,r)*pow(v2,-1,r))%r
                need(z2==(nn*v2-ell*w2)%r,"cusp zero index orientation")
                phase_cases+=1
print(phase_cases,"exact CRT/cusp phase cases; error ceilings",*[float(m) for m in M])
