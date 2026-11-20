from fractions import Fraction
from math import comb, isqrt, prod

def valuation(unit, p):
    num, den = unit.numerator, unit.denominator
    count = 0
    while num % p == 0:
        num //= p
        count += 1
    while den % p == 0:
        den //= p
        count -= 1
    return count, num, den

def hilbert(a, b, p):
    alpha, an, ad = valuation(Fraction(a), p)
    beta, bn, bd = valuation(Fraction(b), p)
    mod = 8 if p == 2 else p
    u, v = an * pow(ad, -1, mod) % mod, bn * pow(bd, -1, mod) % mod
    if p == 2:
        exponent = ((u-1)*(v-1)//4) + alpha*((v*v-1)//8) + beta*((u*u-1)//8)
        return (-1)**(exponent % 2)
    legendre = lambda a: 1 if pow(a, (p-1)//2, p) == 1 else -1
    return (-1)**((alpha*beta*((p-1)//2)) % 2)*legendre(u)**(beta % 2)*legendre(v)**(alpha % 2)

def hasse(coefficients, p):
    return prod(hilbert(a,b,p) for i,a in enumerate(coefficients) for b in coefficients[i+1:])

def require(condition):
    if not condition:
        raise AssertionError("exact finite check failed")

require(hilbert(2,-2,2)==1 and hilbert(2,Fraction(3,2),2)==-1)
for j in range(0,23,2):
    planes = [2,Fraction(3,2)]*j+[2,-2]*(22-j)
    require(hasse(planes,2)==-1)
require(comb(44,2)%2==0 and comb(22,2)%2==1)
model=[1]*42+[7,7]
require([hasse(model,p) for p in [2,3,5,7,11]]==[-1,1,1,-1,1])
for c in [3,21,63]:
    require([hasse([c*x for x in model],p) for p in [2,3,5,7,11]]==[-1,1,1,-1,1])
k2=Fraction(99**2, 2)*Fraction(28,63)
require(k2 == 2178 and (22-int(k2))//2 % 2 == 0)
known=[9,21,49,81,189,441,729,1029]
rows=[(h,44-valuation(Fraction(h),3)[0],44-valuation(Fraction(h),7)[0]) for h in known if isqrt(h)**2==h and h%49==0]
require(rows==[(49,44,42),(441,42,42)])
for p, target in [(3,1),(7,-1)]:
    d=[(a,b) for a in (1,2) if a%p for b in (1,2) if b%p and hilbert(p*a,p*b,p)==target] if p==3 else [(a,b) for a in (1,3) for b in (1,3) if hilbert(p*a,p*b,p)==target]
    require(d and all((pow(a*b%p,(p-1)//2,p)==1)==(p==7) for a,b in d))
print("Local Hasse signs, characteristic congruence, and surviving index rows verified:", rows)
