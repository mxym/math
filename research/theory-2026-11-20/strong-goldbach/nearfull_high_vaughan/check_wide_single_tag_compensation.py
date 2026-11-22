"""Rational arithmetic for the actual single-tag rank compensation."""
from fractions import Fraction as Q


def need(x, name):
    if not x:
        raise ArithmeticError(name)


def log_bounds(x):
    need(x >= 1, "logarithm domain")
    e = 0
    while x > 2:
        x /= 2
        e += 1

    def series(v):
        t = (v - 1)/(v + 1)
        lo = 2*sum((t**(2*i+1)/(2*i+1) for i in range(20)), Q(0))
        return lo, lo+2*t**41/(41*(1-t*t))

    a, b = series(Q(2))
    c, d = series(x)
    return e*a+c, e*b+d


def J3_bounds(left, nodes=4096):
    right = Q(1, 3)
    h = (right-left)/nodes
    lo = hi = Q(0)
    dn = 10**18
    for i in range(nodes+1):
        t = left+i*h
        a, b = log_bounds((1-2*t)/t)
        if i > 0:
            lo += Q((h*a/(t*(1-t))*dn)//1,dn)
        if i < nodes:
            hi += Q(-((-h*b/(t*(1-t))*dn)//1),dn)
    return lo, hi


k = 1/Q(".994")
amin, amax = Q(".00051"),Q(".00060")
qmin, qmax, lev = Q(".5022"), Q(".5086"), Q(".5020")
need((56*qmax-17)/23 == Q(".4992") < Q(".4996"), "dispersion split lower")
need(Q(".4996") < lev < qmin, "long genuine prime rail")
need(Q(".490")+Q(".006")+amax <= Q(".4996"), "tagged A moduli")
need(Q(".499")+amax <= Q(".4996"), "tagged B moduli")
need(Q(".498")+amin>Q(".498505"), "actual B cap derivative")
need(1-k*Q(".000505")>Q(".9994"), "same tag coefficient")
need(Q(".486")-amax>Q(".4853") and (1-Q(".4853"))/Q(".4853")<Q("1.063"), "true H chart")
need(1+k*Q(".491")<Q("1.50"), "H variation")
need((1-Q(".490"))/Q(".490")<Q("1.05"), "H affine chart")
need((lev-Q(".4853"))/2<Q(".014") and 1-qmin-Q(".014")<Q(".4853"), "true source gcd rails")

e = 2*k*amax/(lev-amax)
h1 = 2*Q("1.063")*amax*Q("1.50")/(lev-amax-Q(".490"))
h2 = 2*Q("1.05")*k*amax*Q(".008")/(lev-amax-Q(".498"))
c = 2*Q("1.001")*(amax-Q(".0005"))/(lev-amax-Q(".498"))
b = 2*k*amax*Q(".002")/(Q(".498")*(lev-amax-Q(".5")))
r3 = h1+h2+c+b
need(e<Q(".00242"), "genuine E upper")
need(r3<Q(".234"), "genuine rank-three upper")
need(k*amax<Q(".00061") and Q(".00061")+Q(".00242")+Q(".234")<Q(".238"), "high opposite upper")

u0,u1=(1-qmax)/Q(".014"),(1-qmin)/Q(".014")
need(log_bounds(u1-1)[1]<Q("3.56"), "J2 upper at .014")
need(1/u0<Q(".0285"), "kept rank-four integral")
j014 = J3_bounds(Q(".0285"),2048)[0]
need(j014>Q("5.424"), "J3 lower at .014")
need(log_bounds(Q(100,57))[1]<Q(".57"), "Buchstab gross elementary maximum")
u0,u1=(1-qmax)/Q(".045"),(1-qmin)/Q(".045")
need(u1<Q("11.063") and log_bounds(u0-1)[0]>Q("2.294"), "J2 lower at .045")
tiny0,tiny1=J3_bounds(1/u0)[0],J3_bounds(1/u1)[1]
need(tiny0>Q("1.91") and tiny1<Q("1.949"), "J3 bounds at .045")
need(-1+Q("2.294")-Q("1.949") == -Q(".655"), "higher-rank signed numerator")
need(Q(".57")*Q("11.063")-1-Q("2.294")-Q("1.91")<Q("1.102"), "higher-rank gross numerator")

need(1+k*(1-qmax)>Q("1.49") and 1/(1-qmin)>2, "prime source profile")
need(log_bounds(amax/amin)[0]>Q(".16"), "actual single-tag harmonic")
angular=(qmax-qmin)*Q("1.49")*2*Q(".16")
basic=Q(".9994")*Q("5.424")-Q("1.238")*Q("3.56")
allr=basic-Q("1.1187")*Q(".655")-Q(".1193")*Q("1.102")
need(angular*basic>Q(".0030"), "paired ranks three and four")
need(angular*allr>Q(".00045"), "disjoint higher-rank debit too")
print(f"E upper {float(e):.12f}; signed rank-three debit upper {float(r3):.12f}")
print(f"J3(.014) lower {float(j014):.12f}; J3(.045) in ({float(tiny0):.12f}, {float(tiny1):.12f})")
print(f"rank-three/four signed coefficient > {float(angular*basic):.12f}")
print(f"high-rank inclusive coefficient > {float(angular*allr):.12f}")
