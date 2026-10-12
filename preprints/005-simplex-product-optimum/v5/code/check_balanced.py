#!/usr/bin/env python3
from fractions import Fraction as F
from math import factorial

LOG_TERMS = 48
PI_LO = F(333, 106)
PI_HI = F(355, 113)
THRESH = F(131, 125)  # 1.048
RATE_LO = F(14267, 5000)  # 2.8534

def require(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def atanh_log_interval_unit(y, terms=LOG_TERMS):
    # Rigorous interval for log(y), 1 <= y < 2, via
    # log y = 2 atanh((y-1)/(y+1)).
    require(F(1) <= y < F(2), f"bad unit argument {y}")
    if y == 1:
        return F(0), F(0)
    z = (y - 1) / (y + 1)
    z2 = z * z
    power = z
    s = F(0)
    for n in range(terms):
        s += power / (2*n + 1)
        power *= z2
    lo = 2 * s
    # power is z^(2*terms+1), first omitted power.
    rem = 2 * power / ((2*terms + 1) * (1 - z2))
    return lo, lo + rem

# Exact log 2 interval directly uses z=1/3.
def ln2_interval(terms=LOG_TERMS):
    z = F(1, 3)
    z2 = z*z
    power = z
    s = F(0)
    for n in range(terms):
        s += power / (2*n + 1)
        power *= z2
    lo = 2*s
    rem = 2*power / ((2*terms + 1)*(1-z2))
    return lo, lo+rem

LN2_LO, LN2_HI = ln2_interval()

def log_interval(x):
    x = F(x)
    require(x > 0, "log input must be positive")
    k = 0
    y = x
    while y >= 2:
        y /= 2
        k += 1
    while y < 1:
        y *= 2
        k -= 1
    ly_lo, ly_hi = atanh_log_interval_unit(y)
    if k >= 0:
        return k*LN2_LO + ly_lo, k*LN2_HI + ly_hi
    return k*LN2_HI + ly_lo, k*LN2_LO + ly_hi

def log_lo(x):
    return log_interval(x)[0]

def log_hi(x):
    return log_interval(x)[1]

def g(n):
    return F(n**n, factorial(n)) if n else F(1)

def simplex_R(p):
    return (p+1)*g(p)

def log_2pi_lo():
    return log_lo(2*PI_LO)

def log_2pi_hi():
    return log_hi(2*PI_HI)

L2PI_LO = log_2pi_lo()
L2PI_HI = log_2pi_hi()

def logC_upper(t, p):
    c = F(1, t+1)
    c0 = F(p) + c
    return (
        F(t,2)*log_hi(t)
        + F(t-1)
        + F(1,12*p)
        + F(t-1,2)*(L2PI_HI + log_hi(c0))
        - F(t-1)*log_lo(p+1)
    )

def seed_upper_log_rate(t, p):
    T = t*t
    c = F(1,t+1)
    return (log_hi(simplex_R(p)) + logC_upper(t,p)/F(T-1)) / (F(p)+c)

def iterate_exact(t, p, steps):
    d = p
    a = F(1,p+1)
    R = simplex_R(p)
    T = t*t
    for _ in range(steps):
        dn = T*d+t-1
        D = F(t) * (a**(t-1)) * g(dn) / (g(t*d)**t)
        R = (R**T) * D
        d = dn
        a /= t
    return d, a, R

def level_upper_log_rate(t,p,steps):
    d, a, R = iterate_exact(t,p,steps)
    T=t*t
    c=F(1,t+1)
    return (log_hi(R)+logC_upper(t,p)/F(T-1))/(F(d)+c)

def B_interval(t,p):
    T=t*t
    c=F(1,t+1)
    A=F(1)-c/F(2)
    alpha=F(t,2*(T-1))
    eps=F(1,12*p*(T-1))
    lo=(
        A*log_lo(p+1)
        - F(1,2)*log_hi(p)
        - (F(1)-c)/F(2)*L2PI_HI
        + alpha*log_lo(t)
        + eps
    )
    hi=(
        A*log_hi(p+1)
        - F(1,2)*log_lo(p)
        - (F(1)-c)/F(2)*L2PI_LO
        + alpha*log_hi(t)
        + eps
    )
    return lo,hi

def Bprime(t,p):
    T=t*t
    c=F(1,t+1)
    A=F(1)-c/F(2)
    return A/F(p+1)-F(1,2*p)-F(1,12*(T-1)*p*p)

def F20_interval(p):
    # Tail majorant for all t >= 20.
    lo=(
        log_lo(p+1)-F(1,2)*log_hi(p)
        -F(10,21)*log_hi(6)
        +F(1,38)*log_lo(20)
        +F(1,4788*p)
    )
    hi=(
        log_hi(p+1)-F(1,2)*log_lo(p)
        -F(10,21)*log_lo(6)
        +F(1,38)*log_hi(20)
        +F(1,4788*p)
    )
    return lo,hi

def F20prime(p):
    return F(1,p+1)-F(1,2*p)-F(1,4788*p*p)

def main():
    # The comparison threshold itself.
    require(log_lo(RATE_LO) > THRESH,
            "failed to certify log(2.8534) > 1.048")

    # Finite core: the crude all-level Robbins majorant already excludes
    # every pair except t=2 and p<=7.
    core_checked=0
    core_exceptions=[]
    for t in range(2,20):
        for p in range(1,20):
            u=seed_upper_log_rate(t,p)
            if t==2 and p<=7:
                core_exceptions.append((t,p))
            else:
                require(u < THRESH, f"finite core not excluded: t={t}, p={p}")
                core_checked += 1
    require(core_exceptions == [(2,p) for p in range(1,8)],
            f"unexpected exception list {core_exceptions}")

    # Two exact recurrence levels plus the same all-level tail bound exclude
    # every exceptional seed except the known winner p=5.
    sharpened=0
    for p in [1,2,3,4,6,7]:
        u=level_upper_log_rate(2,p,3)
        require(u < THRESH, f"three-level sharpening failed for p={p}")
        sharpened += 1

    # For 2 <= t <= 19 and p >= 20, prove the logarithmic majorant decreases
    # from p=20 onward. B''<0 is an analytic rational inequality in the paper;
    # here we certify H_t(20)>0 and the starting value < 0.04.
    tails=0
    for t in range(2,20):
        c=F(1,t+1)
        blo,bhi=B_interval(t,20)
        bp=Bprime(t,20)
        Hlo=blo-(F(20)+c)*bp
        require(Hlo>0,f"H_t(20) not positive for t={t}")
        require(bhi/(F(20)+c)<F(1,25),
                f"p-tail start too large for t={t}")
        tails+=1

    # For t>=20, the universal F(p)/p majorant is decreasing from p=8.
    # Check p=1..8 and the derivative sign certificate at p=9.
    for p in range(1,10):
        flo,fhi=F20_interval(p)
        require(fhi/F(p)<F(6,125),
                f"large-t majorant too large at p={p}")
    flo,_=F20_interval(9)
    Hlo=flo-F(9)*F20prime(9)
    require(Hlo>0,"large-t monotonicity certificate failed at p=9")

    # Independently replay the inherited lower endpoint for the winner.
    d,a,R6=iterate_exact(2,5,6)
    require(d==21845 and a==F(1,384),
            "winner closed forms disagree with inherited v2")
    require(RATE_LO**(3*d+1) < 3*R6**3,
            "winner lower-endpoint integer inequality failed")

    print("PASS: balanced homogeneous simplex-orbit classification certificate")
    print("finite_core_excluded =", core_checked)
    print("finite_core_exception_pairs =", len(core_exceptions))
    print("three_level_exceptions_excluded =", sharpened)
    print("p_tail_arities_certified =", tails)
    print("large_t_tail = all t>=20, all p>=1")
    print("winner = (t,p)=(2,5)")
    print("winner_dimension_level6 =", d)
    print("winner_lower_endpoint = 14267/5000")
    print("competitor_log_upper = 131/125")
    print("arithmetic = Fraction only; logarithms enclosed by rational atanh series")
    print("checks remain active under python -O")

if __name__=="__main__":
    main()
