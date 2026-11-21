"""Exact arithmetic guardrails for the theorem. No numerical claims on primes."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path

def check(b,m):
    if not b: raise ArithmeticError(m)

a,b,c=map(F,(".18",".218",".092")); h=F(".00001")
d=F(".0001"); q1,q2,q3=map(F,(".398001",".010098",".092001"))
lev=F(".01008"); T=F(".01"); lam=F(".001")
check(q1+q2+q3==F(".5")+d and 0<d<F(".001"), "product")
check(40*d < q2 < F(1,20)-7*d, "second exponent")
check(F(".1")+12*d-q2 < q3 < F(".1")-4*d-F(3,5)*q2, "third exponent")
check(a+b<q1 and c<q3 and lev<q2, "both central endpoints")
check(tuple(1//(z-h) for z in (a,b,c))==(5,4,10), "weight multiplicity")
for A in (sum(ts) for ts in product(*[(z-h,z) for z in (a,b,c)])):
    check(1 <= (F(".5")-A)/T <= F("1.003"), "Dickman bias scale")
    check((1-A)/T>=51,"Buchstab argument")
    check(F(".5")-A<min(a,b,c)-h,"all residual primes avoid marks")
check(lev/T==F("1.008") and F("1.003")/(1-lam)<lev/T,"factorial separation")
# Calibration and contrasting marginals, using formal non-actual numbers only.
from random import Random
rng=Random(7011973)
for i in range(100):
    M=F(rng.randrange(1,200),7); I=F(rng.randrange(1,30),190)
    for prime_mass, predicted_net in ((M,0),(M+I,-I)):
        H=4*M-prime_mass; Lo=-3*M
        check(H+Lo==predicted_net, "mixed sign")
# Arbitrary tiny shift of at most eta*H loses at most eta*(4M+actual_prime_mass).
# Check positivity and colour support of the finite-difference score.
for nums in ((3,4,11,15),(5,6,7),(2,8,13,17,19)):
    tot=sum(nums); degree=12
    score=sum((-1)**sum(bits)*max(F(0),1-2*sum(n*v for n,v in zip(nums,bits))/F(tot))**degree
              for bits in product((0,1),repeat=len(nums)))
    check(score>0,"small exact convex finite difference control")
    n=len(nums)
    check(abs(1-score)<= (2**n-1)*max(F(0),1-F(2*min(nums),tot))**degree,"finite-rank error")
data=Path(__file__).with_name("Proof.md").read_bytes()
check(not any(x<32 and x not in (10,) for x in data),"proof control byte")
print("Maynard exponent rails; endpoint/cut margins; multiplicity 200; Dickman precision; score/channel controls: OK")
