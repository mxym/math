"""Exact rails, varying CRT moduli, and phase collision checks."""
from fractions import Fraction as F
from itertools import product
from math import gcd

def need(v,x):
    if not v:
        raise RuntimeError(x)

for alo,ahi,blo,bhi,xdiag,xoff in (
        (".357",".387",".530",".600",".9946",".99645"),
        (".357",".367",".600",".629",".9991",".98595")):
    maxima=[F(0),F(0)]
    for a,b,s,d,e,g in product((F(alo),F(ahi)),(F(blo),F(bhi)),
             (F(".10"),F(".14")),(F(0),F(".001")),(F(0),F(".001")),(F(0),F(".0001"))):
        z=F(".0002")
        t=a+b+s+d+e+g-1+z
        need(t<s and s+t<a, "no wrap and short frequency")
        need(b-a-s < a/2+s, "whole period relative bound")
        diag=1-s-b-g+b+(s+t)/2
        off=1-s-b-g+b/2+s+t+a/4+d/2+s/2
        need(diag==1+(a+b+d+e-1-g+z)/2,"summed diagonal")
        need(off==5*a/4+b/2+3*s/2+3*d/2+e+z,"summed off-diagonal")
        maxima=[max(maxima[0],diag), max(maxima[1],off)]
    need(maxima==[F(xdiag),F(xoff)] and max(maxima)<1, "power margins")

s,a,b=F(".139"),F(".450"),F(".545")
need(s+a/2+5*b/4>1 and 3*s/2+5*a/4+b/2>1 and s+a+b>1,
     "witness beyond the union")

# The exponents represent fractions modulo 1; check varying-modulus CRT on
# every unit in a small but nontrivial family, with common composite P=p*d.
p,d=131,15
P=p*d
checks=0
for s,sp in product((7,11,13), repeat=2):
    for k,kp in product((-2,-1,1,2),repeat=2):
        if (s,k)==(sp,kp):
            continue
        lcm=P*s if s==sp else P*s*sp
        c=k-kp if s==sp else k*sp-kp*s
        need(gcd(c,p)==1 and gcd(c,s*sp)==1, "off-diagonal numerator units")
        for r in (17,19,23,29,31,37,41,43):
            if gcd(r,lcm)>1:
                continue
            v=F(k*pow(r,-1,s*P),s*P)-F(kp*pow(r,-1,sp*P),sp*P)
            u=F(c*pow(r,-1,lcm),lcm)
            need((u-v).denominator==1, "combined phase exact")
            checks+=1

print(checks,"exact varying-modulus phase cases; all rational rails and uncovered profile verified")

# Raised exact dual endpoints and the disjoint forward strip ceilings.
need(F(".140")+F(".860")*F(".001")+F(".359")==F(".49986")
     < (1-F(".0001"))/2,"ordinary BV short-v seam")
need(F(".140")+F(".860")*F(".400")+F(".001")+F(".499")==F(".984"),
     "raised reflected geometric floor")
for a,b,s,diag_m,off_m in (
        (F(".460"),F(".5095"),F(".10"),F(".98585"),F(".999575")),
        (F(".400"),F(".525"),F(".14"),F(".96360"),F(".998950")),
        (F(".375"),F(".535"),F(".14"),F(".95610"),F(".998950"))):
    kind=0 if a==F(".460") else 1
    s_over=F(".14")
    ahalf_plus_s=F(".360") if not kind else a/2+s
    wrap_a=F(".720") if not kind else a+2*s_over
    need(a+b+F(".0023")<1 and wrap_a+F(".0023")<1,"forward wrap rails")
    need(1+(a+b+F(".0022")-1)/2==diag_m,"forward diagonal ceiling")
    need(ahalf_plus_s+5*b/4+F(".0027")==off_m<1,"forward off-diagonal ceiling")
print("raised dual and three forward strips verified")
