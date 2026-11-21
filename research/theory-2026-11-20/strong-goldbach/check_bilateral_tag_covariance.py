"""Exact finite sanity checks of the double-tag CRT and bivariate local coefficients."""
from fractions import Fraction as F
from itertools import permutations, product
from math import gcd

def need(ok, where):
    if not ok:
        raise AssertionError(where)

def phi(n):
    return sum(gcd(i,n)==1 for i in range(n))

def crt_zero_residue(A,B,r):
    return (r*pow(A,-1,B) % B)*A

cases=0
for s,a,b in permutations([3,5,7,11],3):
    for N in range(8,60,2):
        if gcd(N,s*a*b)!=1:
            continue
        for d,e in product([1,13,17,19],repeat=2):
            if gcd(d,e)!=1 or gcd(d*e,N*s*a*b)!=1:
                continue
            A,B=a*d,b*e
            q0=crt_zero_residue(A,B,N*pow(s,-1,B))
            q_all=[q0+k*A*B for k in range(N)]
            need(all(q%a==q%d==(N-s*q)%b==(N-s*q)%e==0 for q in q_all), "two tags")
            need(len(set(q%N for q in q_all))==N, "unit spread")
            need(sum(gcd(q,N)==1 for q in q_all)==phi(N), "exact density")
            cases+=1

# (1-X)(1-Y)*(1-XY/(1-X)/(1-Y)) = 1-X-Y, exact coefficients.
for i,j in product(range(9), repeat=2):
    def cc(a,b):
        return (1 if a==b==0 else -1 if a>=1 and b>=1 else 0)
    C=cc(i,j)-cc(i-1,j)-cc(i,j-1)+cc(i-1,j-1)
    need(C==({(0,0):1,(1,0):-1,(0,1):-1}.get((i,j),0)), "signed Euler factor")

# Derivative bounds for f outside its fixed flattening.
need(F("3.14")*F(".039")/F(".310")>F(".395"), "minimum sine argument")
need(F(22,7)*F(".046")/F(".310")<F("1.57"), "sine monotonic interval")
need(F(".395")-F(".395")**3/6>F(".38"), "sine lower")
need(F(".95")*F(".85")*10*F(".38")>3, "strict derivative")
need(F(".859")*(1-2*F(".141"))**2>F(".4"), "physical W lower")

for K,J in product(range(27),repeat=2):
    R=K*(K-1)*J//2+K*J*(J-1)//2
    need(0<=K*J-int(K>=1 and J>=1)<=R, "literal any-tag mask")
    need(0<=K*J-int(K==J==1)<=2*R, "literal exact-one mask")
print(cases,"exact CRT cases; 81 local Euler coefficients; 729 count-pairs; strict derivative verified")
