"""Directed rational certificate; every check also executes under python -O."""
from fractions import Fraction as Q

GRID = 10**12


def check(cond, explanation):
    if not cond:
        raise ArithmeticError(explanation)


def down(x):
    return Q((x * GRID).__floor__(), GRID)


def up(x):
    return Q((x * GRID).__ceil__(), GRID)


def logarithm(x):
    check(x >= 1, "log domain")
    z = (x - 1) / (x + 1)
    z2 = z * z
    power = z
    value = Q(0)
    for i in range(11):
        value += 2 * power / (2*i+1)
        power *= z2
    return down(value), up(value + 2*power/(23*(1-z2)))


def upper_integral(a, b, ub):
    h = (b-a) / 1024
    return h * sum(up(ub(a+h*i, a+h*(i+1))) for i in range(1024))


theta, theta_prime = Q(479, 1000), Q(499, 1000)
s0 = 10*theta
check(Q(1) < (theta-Q(1, 3))*10 < (theta-Q(1, 10))*10 < 4,
      "direct upper f range")
check(4 < s0 < 6, "direct lower f range")
check(1 <= theta_prime / Q(249, 1000) <= 3, "switched F range")
head = logarithm((s0-1)*(3*theta-1))[0]/theta
# v+1 times s0-v-1 is decreasing for v >= 2; the other two
# factors are bounded using the correct separate endpoints.
loss = upper_integral(Q(2), s0-2, lambda a, b:
    logarithm(b-1)[1]/a * logarithm((a+1)*(s0-a-1)/(s0-1))[1])/theta
# t(1-t) is increasing for t <= 1/3; log(2-3t) decreases.
switch = upper_integral(Q(1, 10), Q(1, 3), lambda a, b:
    logarithm(2-3*a)[1]/(a*(1-a)))/theta_prime
net = down(head-loss-switch)
m_lo, m_hi = logarithm(Q(73, 27))
check(net > Q(335, 10000), "direct-minus-switch margin")
check(switch < 1, "switched upper less than one")
check(m_lo > Q(994, 1000) and m_hi < 1, "source mass enclosure")
count = net*m_lo - switch*(1-m_lo)
mass = m_lo - switch/(switch+net)
check(count > Q(27, 1000), "true representation lower")
check(mass > Q(27, 1000), "productive smaller-label mass")
print("direct minus switch safe lower:", net)
print("switched safe upper:", float(switch))
print("true representation lower:", float(count))
print("productive smaller-label mass lower:", float(mass))
