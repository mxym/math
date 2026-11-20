"""Independent arithmetic controls for the unsigned Conway reduction.
No graph search is performed. The paper proves the conditional theorem.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial

def check(ok):
    if not ok:
        raise RuntimeError("arithmetic control failed")

def hilbert(a, b, p):
    def split(x):
        x, k = Q(x), 0
        while x.numerator % p == 0:
            x /= p
            k += 1
        while x.denominator % p == 0:
            x *= p
            k -= 1
        mod = 8 if p == 2 else p
        return k, (x.numerator * pow(x.denominator, -1, mod)) % mod
    i, u = split(a)
    j, v = split(b)
    if p == 2:
        e = ((u-1)//2)*((v-1)//2)+i*((v*v-1)//8)+j*((u*u-1)//8)
        return (-1)**(e % 2)
    def leg(z):
        return 1 if pow(z,(p-1)//2,p)==1 else -1
    return (-1)**((i*j*((p-1)//2))%2) * leg(u)**(j%2) * leg(v)**(i%2)

def hasse(form, p):
    h = 1
    for a, b in combinations(form, 2):
        h *= hilbert(a, b, p)
    return h

def model_checks():
    # Any other odd finite prime sees only units in all these forms.
    physical = [1]*42+[7,7]
    signed = [1]*20+[7,7]
    anti_physical = [Q(2*x,7) for x in signed]
    sym_model = [7]*22  # established by scaling to the standard form
    for p in [2, 3, 5, 7, 11, 13]:
        check(hasse(physical,p) == (-1 if p in (2,7) else 1))
        check(hasse(anti_physical,p) == 1)
        check(hasse(sym_model,p) == hasse(physical,p))
        check(hasse([7*x for x in sym_model],p) == 1)
    check(Q(49,4)+14+Q(84,64) == Q(21,4)**2)
    pi_lower = Q(314,100)
    bounds = (Q(2**15*factorial(7),factorial(15)*12)*pi_lower**7,
              pi_lower**7/(16*factorial(7)))
    check(bounds[0] > Q("0.0256118267"))
    check(bounds[1] > Q("0.0352392080"))
    check(2**15//2**8 == 128 and 2*128 == 256)
    print("Exact Hilbert factors, axis metric and both strict packing comparisons agree.")

def d12_checks():
    n = 12
    def canon(x):
        # Integral residues modulo 2D12 have a parity word and a half-sum bit.
        # Translation by the all-ones vector accounts for the other coset of 2D12+.
        def key(z):
            rem = tuple(i % 2 for i in z)
            return rem, (sum(z)-sum(rem))//2 % 2
        return min(key(x), key(tuple(i+1 for i in x)))
    all_int = {}
    for b in product(range(2), repeat=n):
        if sum(b)%2:
            continue
        for add in range(2):
            x = (b[0]+2*add,)+b[1:]
            c = canon(x)
            norm = sum(i*i for i in x)%4
            check(c not in all_int or all_int[c] == norm)
            all_int[c]=norm
    zeros = {c for c,r in all_int.items() if r == 0}
    norm4=set()
    for k in range(n):
        x=[0]*n
        x[k]=2
        norm4.add(canon(x))
    for inds in combinations(range(n),4):
        for signs in product((-1,1),repeat=4):
            x=[0]*n
            for k,s in zip(inds,signs): x[k]=s
            norm4.add(canon(x))
    check(len(all_int)==2048 and len(zeros)==992 and len(norm4)==991)
    check(norm4 == zeros-{canon([0]*n)})
    print("D12+ integral residues: all 991 nonzero norm-0 classes have norm-4 representatives.")

if __name__ == "__main__":
    model_checks()
    d12_checks()
