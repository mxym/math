"""Outward ordinary density/linear-receiver enclosure and exact signed ledger."""
from fractions import Fraction as Fr
from math import inf, nextafter, prod

def require(x, reason):
    if not x:
        raise ArithmeticError(reason)

P, a = 10000, 800
dn = lambda x: nextafter(x, -inf)
up = lambda x: nextafter(x, inf)
Z, one = (0., 0.), (1., 1.)

def rat(x, y=1):
    return dn(x / y), up(x / y)

def add(a, b):
    return dn(a[0]+b[0]), up(a[1]+b[1])

def neg(a):
    return -a[1], -a[0]

def sub(a, b):
    return add(a, neg(b))

def mul(a, b):
    v = [x*y for x in a for y in b]
    return dn(min(v)), up(max(v))

def div(a, b):
    require(b[0] > 0, "positive denominator")
    return mul(a, (dn(1/b[1]), up(1/b[0])))

def pos(a):
    return max(a[0], 0), max(a[1], 0)

B = []
for sign in (1, -1):
    values = [Z]*a
    prefix = [Z]*(a+1)
    for i in range(a, P+1):
        edge = ((prefix[i-a][0], prefix[i-a+1][1]) if sign == 1 else
                (prefix[i-a+1][0], prefix[i-a][1]))
        v = div(add(one, edge), (rat(i,P)[0], rat(i+1,P)[1]))
        # t B_+ = 1 + integral B_+; t B_- = -(1 + integral B_-).
        # B_+ is nonnegative; B_- is nonpositive by Dickman's equation.
        v = pos(v) if sign == 1 else neg(pos(v))
        values.append(v)
        prefix.append(add(prefix[-1], div(v, (P,P))))
    B.append(values)

def F(i):
    b = P//2-i
    require(b >= 0, "supported profile")
    return rat(b**4*(44*P**2-112*b**2), P**6)

def profile(i):
    return F(i+1)[0], F(i)[1]  # nonincreasing on this support

m = B[0][P]
for i in range(a, 5000):
    v = mul(profile(i), mul(B[1][i], B[0][P-i-1]))
    m = add(m, div(v, (P,P)))

U = [(2., 2.)]*2401 + [Z]*2600
K = [Z]*5001
for i in range(1600, 5000):
    j = i-a
    K[i+1] = add(K[i], div((U[j][0], U[j+1][1]), (j,j+1)))
    if i >= 2400:
        U[i+1] = add(U[i], div((K[j][0], K[j+1][1]), (j,j+1)))
lower = div(K[5000], rat(1,2))
upper = div(U[5000], rat(1,2))

for i in range(a, 4999):
    d = 5000-i-1
    u, k = div(U[d], rat(d,P)), div(K[d], rat(d,P))
    E = pos(div(add(B[0][i],B[1][i]),(2,2)))
    O = pos(div(sub(B[0][i],B[1][i]),(2,2)))
    lower = add(lower, div(mul(profile(i), sub(mul(k,E),mul(u,O))),(P,P)))
    upper = add(upper, div(mul(profile(i), sub(mul(u,E),mul(k,O))),(P,P)))
# On the final cell D <= 1/P, F(s) U_1(D) <= 88 D^3, k_1=0.
tail = mul(rat(88,P**4), (0., max(1., B[0][4999][1])))[1]
low_coeff = dn(lower[0]-tail)
up_coeff = up(upper[1]+tail)
require(Fr(low_coeff) > Fr("3.25984865"), "lower receiver")
require(Fr(up_coeff) < Fr("3.72566993"), "upper receiver")
require(Fr(m[1]) < Fr("3.503"), "ordinary mass of A")

# Constants on the unchanged .003 tiny and original W source.
b,c,w,j = Fr(".003"),Fr(".0135"),Fr(".070"),14
z = (w+c)/(w-c)
t0 = 16*z**5-20*z**3+5*z
lam = (t0-1)/(t0+1)
g0 = 1+(1+((4*w/(w-c))**5+1)/(t0+1))**2
r0 = (w-c-b)/b
rho = g0/prod(r0-i for i in range(j))*(1+4**j*(1-c-b)/(1-c-b-j*b))
BV, BX, BD, UD, UW = map(Fr, (".009042", ".017667", ".006657", ".007445", ".52844"))
old_abs = Fr(".8")/b*BX**2
new_abs = (672*b**5)**2+(1-lam**2+rho)*old_abs
require(new_abs < Fr(".006105"),"absolute small-pair comparison")
U, K = Fr("3.7257"), Fr("3.2598")
MW, MQ, UQ = Fr(".16921"), Fr(".01701"), Fr(".852")
eps = Fr(1,10**7)
d0_loss = (U-K)*(BV+BD)/2+Fr("3.74")*eps
require(d0_loss < Fr(".003658"),"signed stopped remainder")
T2 = Fr(".2263381")**2-eps**2-Fr(".006105")-(BD+2*BV)*UD
Y2 = (Fr("11.745")+1-2*Fr("3.503")
      -2*(Fr(".226339")*Fr("2.503")+Fr(".003658")+eps)
      -2*(U-1-Fr(".226337"))*MW-2*(UW*BV+UD*MW)+T2)
require(Y2 > Fr("3.785"),"whole nonzero square")

B3 = ((U+K)*Fr(".344")/2+(U-K)*Fr(".350")/2-Fr(".09154")
      + Fr(".55006")*MQ+UQ*Fr(".002527"))
h = sum(map(Fr,(".01933",".00345",".000534",".000078",".0000114")))/2
require(h == Fr(".0117017"),"half envelope harmonic")
B4 = U*(Fr(".0554")+h)+(Fr("3.446")+UQ)*h+Fr(".1212")*MQ
total = Fr(".4018")+Fr("4.251")+Fr("3.785")-2*(B3+B4)
require(total > Fr("5.427"),"remaining genuine 01/02 comparison")

print("ordinary m(A):", m, "receiver lower/upper:", low_coeff, up_coeff)
print("T square lower:", float(T2), "Y square lower:", float(Y2))
print("zero/3, zero/4 costs per orientation:", float(B3), float(B4))
print("magnitude of complete 01/02 adverse upper:", float(total))
