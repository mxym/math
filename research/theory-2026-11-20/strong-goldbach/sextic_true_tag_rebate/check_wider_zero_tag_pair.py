"""Outward full .110 rough-pair covariance, plus the original low mixed strip."""
from hashlib import sha256
from math import factorial as fac, isqrt
from pathlib import Path

root = Path(__file__).resolve().parent
base = root / "check_rough_positive_credit.py"
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "9aea10c73278ce69f67cef7c01fcd32a01a47cdc6228449f57070203960633ba"
):
    raise ArithmeticError("different ambient checker")
prefix, sep, _ = raw.decode().partition('a=F(".15")')
if not sep:
    raise ArithmeticError("ambiguous ambient checker")
exec(compile(prefix, str(base), "exec"))

a = F(".110")
theta = F(".499")
# Downward fixed rational argument to the audited integer Dickman-2 CDF.
u = F(int(theta * 30000 / a), 30000)
C = 1 / (a * a * rho_bounds(u))
k, U = F(".549") / a, F(".575") / a

# Positive rank-two and rank-three witness layers, innermost boxes only.
D, bins = 1000, 160
a0 = int(a * D)
den = 4 * D**6
def raw_F(t):
    z = D - 2*t
    return z**4 * (11*D*D - 7*z*z) if z > 0 else 0

P = [raw_F(t) for t in range(D+1)]
psi = [P[t] - P[D-t] for t in range(D+1)]
mass = [0]*(bins+1)
n2 = n3 = 0
def add(score, volume):
    j = min(bins, (score*bins-1)//den)
    if j > 0:
        mass[j] += volume

for i in range(a0, D//2):
    add(den-P[i], D*S//((i+1)*(D-i)))
    n2 += 1
for i in range(a0, D//3+1):
    for j in range(i+1, (D-i-3)//2+1):
        v = D-i-j
        require(v-2 >= j+1)
        add(den-psi[i]-psi[j]-psi[v-2], D*S//((i+1)*(j+1)*v))
        n3 += 1
means = [F(sum(mass[j:]), S) for j in range(1, bins+1)]
plus = sum(max(0, k*(u+v)-C) for u in means for v in means) / bins**2

def sqrt_hi(x):
    scale = 10**13
    P, Q = x.numerator*scale*scale, x.denominator
    j = isqrt(P//Q)
    return F(j+(j*j*Q<P), scale)
def sharp(t):
    z = max(F(1,2)-t, 0)
    return 44*z**4 - 112*z**6

# Complete adverse envelope on the same literal rough pair.
h = F(".14")
z = 1-2*a
require(528-3360*(F(1,2)-a)**2 > 0)
require(z**3 * (11-7*z*z) < 4 and 33-35*z*z > 0)
require(1-sharp(a)-sharp(h)+sharp(a+h) > 0)
m3 = max(0, 2*sharp(a)-1-sharp(2*a))*(h-a)**2/(2*a*a*(1-2*h))
A = 1-4*a
qbar = 4*a*a+2*a*A+2*A*A/5
d = qbar-F(11,35)
m4 = 1680*A**3/(fac(4)*fac(3)) * (sqrt_hi(d*d+2*A**4/175)+d)/2
A = 1-5*a
qbar = 5*a*a+2*a*A+A*A/3
qroot = sqrt_hi(qbar)
m5 = (10080*qroot-1056/qroot)*A**4/(fac(5)*fac(4))
m6 = 40320*(1-6*a)**5/(fac(6)*fac(5))
m7 = (2112/a**3+80640*7)*(1-7*a)**6/(fac(7)*fac(6))
require(9*a<1<10*a)
cap9 = F(16896, 9**4)+F(322560, 9**6)
m9 = cap9*(1-9*a)**8/(a**9*fac(9)*fac(8))
minus = 2*U*(m3+m4+m5+m6+m7+m9+2**9*m9)
net = plus-minus
require((n2,n3)==(390,37185))
require(plus>F("1.5797") and minus<F(".64395") and net>F(".935"))
print("full .110 rough pair: ambient, positive, adverse, net",
      float(C), float(plus), float(minus), float(net))

# Keep precisely the lower-tag portion of the already proved C_Q.
mixed = root / "check_mixed_tag_credit.py"
raw = mixed.read_bytes()
if sha256(raw).hexdigest() != (
    "c8fd8207b14e251e4ef7044068acc1effd0d6b7e3a2266bdcc8e90b240c0ced6"
):
    raise ArithmeticError("different mixed checker")
code = raw.decode()
for old, new in (
    ('range(150,500)', 'range(126,500)'),
    ('range(150,334)', 'range(126,334)'),
    ('F(".150")', 'F(".1251")'),
    ('F("3.8")', 'F(".57")/a'),
    ('range(80,125)', 'range(80,110)'),
    ('pos>F(".115328") and neg<F(".058450")',
     'pos>F(".09987") and neg<F(".054735")'),
    ('2*(pos-neg)>F(".113")', '2*(pos-neg)>F(".090")'),
    ('net > .113', 'net > .090'),
):
    if code.count(old)!=1:
        raise ArithmeticError("ambiguous mixed-strip change")
    code=code.replace(old,new)
exec(compile(code, str(mixed), "exec"), {"__file__": str(mixed)})
