"""Exact upper errors for the two whole signed geometric bank masses."""
from fractions import Fraction as Q
from math import factorial


def require(ok, reason):
    if not ok:
        raise RuntimeError(reason)


def bank(a, b, v_max, rank, bound):
    # A compound Poisson law with intensity 1_(a,b] du/u.
    # exp(v_max) > b/a, checked without floating point.
    require(sum(v_max**j / factorial(j) for j in range(9)) > b/a,
            "logarithmic intensity bound")
    require((rank-1)*b < 1 <= rank*b, "first possible boundary rank")

    w = b-a
    m2 = (b*b-a*a)/2
    m3 = (b**3-a**3)/3
    excess = 22*w - 72*(w*w+m2) + 48*(w**3+3*w*m2+m3)

    # P' >= 0 on [1/2,1], so only X>1 has a bad cutoff error.
    t = b*rank
    ratio_poly = v_max * (rank+1)**2 / rank**3
    ratio_exp = 2*v_max / (rank+1)
    require(ratio_poly < 1 and ratio_exp < 1, "geometric tail ratios")
    err1 = ((1+22*t+72*t*t+48*t**3)*v_max**rank/factorial(rank)
            / (1-ratio_poly))
    err2 = 7*(2*v_max)**rank/factorial(rank)/(1-ratio_exp)
    err3 = (2/a)*(2*v_max)**(rank-1)/factorial(rank)/(1-ratio_exp)
    wsum = Q(".146748616")+Q(".077025550")
    net = excess-err1-err2-err3-wsum
    require(net > bound, "strict compensated ordinary source mass")
    print(f"excess {float(excess):.12f}; outward errors "
          f"{float(err1):.12f}, {float(err2):.12f}, {float(err3):.12f}; "
          f"net negative mass > {float(net):.12f}")


bank(Q(".012"), Q(".076"), Q("1.85"), 14, Q(".660"))
bank(Q(".019"), Q(".058"), Q("1.125"), 18, Q(".430"))
require(22*Q(".660") > 14 and 22*Q(".430") > Q("9.3"),
        "signed cross constants")
require(14*Q(".004")+Q("9.3")*(Q(".018")-Q(".004")) > Q(".186"),
        "one-orientation union")
