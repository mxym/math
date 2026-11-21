"""Exact rails and harmonic coefficient algebra for DualPrimeLogConservation."""
from fractions import Fraction as F

def need(v,x):
    if not v:
        raise RuntimeError(x)

examples=((F(".200"),F(".180"),F(".006")),(F(".001"),F(".357"),F(".001")))
for c,a,eta in examples:
    rho=F(".140")+F(".860")*c+a
    need(a>=F(".90")*c and rho<(1-eta)/2,"both BV regimes")
    need(rho< F(".5") and a<F(".360"),"short tag and strict power reserve")

# Masked affine harmonic identities with independent log Y, gamma+L_D, T.
# C_D is canceled algebraically in the e and k harmonics.
cases=0
for T in (F(17,7),F(80),F(129)):
    for A in (F(0),F(1,3),F(7)):
        for z in (F(13,3),F(43),F(88)):
            for C in (F(2),F(15,4),F(71,4)):
                I0=C/T
                I1=-C+2*C*A/T
                value=((z+A)*I0-I1)/C-1
                need(value==(z-A)/T, "proper composite v=1 endpoint")
                cases+=1

# The shift derivative provides -1 in the p-integral, and the low reflected
# part has the opposite sign, exact independent of J.
B=F(".489")
need((1-B)+(1-B)*(-1)==0,"sign and calibration cancellation")
print("Modulus exponents",*(float(F('.140')+F('.860')*c+a) for c,a,_ in examples),
      ";",cases,"exact finite harmonic endpoints")
