"""Exact rational checks for SpectralSubcriticalPrimeProduct.md; also under -O."""
from fractions import Fraction as F
from itertools import product


def need(test, msg):
    if not test:
        raise ArithmeticError(msg)


theta = F(7, 64)
zeta = F(".0002")
Q_loss = F(".0003")
sig0, sig1 = F(".10"), F(".14")
a0, b0, ab1 = F(".359"), F(".499"), F(".997")
de = F(".001")
gmax = F(".0001")
a1, b1 = ab1-b0, ab1-a0

# All copied displayed expressions are compared to independent pre-Cauchy
# exponents on the complete product of the tag triangle and four intervals.
bounds = [(sig0, sig1), ((a0, b0), (a0, b1), (a1, b0)),
          (F(0), de), (F(0), de), (F(0), gmax)]
diag_max = zero_max = eq_max = -F(100)
neq_macro = -F(100)
tested = 0
for s, (a, b), d, e, g in product(*bounds):
    t = s+a+b+d+e+g-1+zeta
    base = 1-s-(a+b)/2-g
    level_same = 2*e+d+s
    level_unequal = level_same+s
    freq = b+e-a
    u = min(freq, level_unequal-e)
    pos = max(F(0), e+freq-level_same)
    # squared norm sizes, independently assembled factor by factor
    norm2_diag = a+b+s+t
    norm2_zero = a+2*s+2*t
    norm2_neq = Q_loss+2*s+b+level_unequal/2+theta+t+2*e+theta*(s-t)-u/2
    norm2_eq = Q_loss+s+b+level_same/2+theta+3*t/2+2*e+pos/2
    diag = 1+(a+b+d+e-1-g+zeta)/2
    nul = s+a+b/2+d+e+zeta
    neq = F(1,2)+s+b/2+3*d/4+2*e-g/2+zeta/2+theta*(1+s-t)/2+Q_loss/2-u/4
    eq = F(1,4)+s/2+a/4+3*b/4+d+9*e/4-g/4+3*zeta/4+theta/2+Q_loss/2+pos/4
    for value, norm in [(diag,norm2_diag),(nul,norm2_zero),(neq,norm2_neq),(eq,norm2_eq)]:
        need(value == base+norm/2, 'displayed exponent mismatch')
    diag_max = max(diag_max, diag)
    zero_max = max(zero_max, nul)
    # eq is a maximum of two affine functions, so checking vertices suffices.
    eq_max = max(eq_max, eq)
    # Each affine branch of the unequal expression is separately bounded,
    # omitting -theta*t/2 for the feasible t >= 0.
    neq_macro = max(neq_macro, F(1,2)+s+(a+b)/4, F(1,2)+s/2+b/2)
    need(t-s <= -F(".0007"), 'frequency / injection gap')
    need(a+b+g+zeta-1 <= -F(".0027"), 'infinity index / level gap')
    need(b-a >= F(".001"), 'prime tags can collide')
    need(a+b+d+e <= F(".999"), 'coupled boundary floor')
    tested += 1
neq_upper = neq_macro+3*de/4+2*de+zeta/2+theta*(1+sig1)/2+Q_loss/2
need(diag_max == F(".9996"), 'diagonal ceiling')
need(zero_max == F(".8897"), 'zero completion ceiling')
need(neq_upper < F(".955"), 'unequal spectral ceiling')
need(eq_max == F(".9809875") and eq_max < F(".982"), 'equal spectral ceiling')

# Exact CRT uniqueness test illustrating the boundary count. Unit condition
# is verified first; the admissible (d,e) are coprime. Check one residue mod de.
crt_tests = 0
for p, r in [(11,17),(19,23),(23,37)]:
    for N in range(40,125,2):
        if N % p == 0 or N % r == 0:
            continue
        t0 = (N*pow(p,-1,r)) % r
        v0 = (N-p*t0)//r
        for d,e in [(1,1),(2,3),(3,4),(4,9),(5,7),(7,3)]:
            residues = [j for j in range(d*e) if (t0+r*j)%d == 0 and (v0-p*j)%e == 0]
            need(len(residues)==1, 'nonunique divisor boundary class')
            crt_tests += 1
print("rational vertices:", tested, "CRT boundary cases:", crt_tests)
print("ceilings:", *(float(z) for z in (diag_max,zero_max,neq_upper,eq_max)))
