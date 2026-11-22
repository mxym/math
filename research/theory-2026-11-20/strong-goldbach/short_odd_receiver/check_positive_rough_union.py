#!/usr/bin/env python3
"""Exact upper of the signed rough-positive union."""
from fractions import Fraction as Q

def need(test, label):
    if not test:
        raise SystemExit("failed: " + label)

a, v, D, b = Q(15,100), Q(498,1000), Q(499,1000), Q(44,100)
w = 1-2*v
k = 1/(1-Q(1,10000))
alpha = 1-k*Q(1,1000)
need(D > b > 2*a and (D-2*a)/2 < a, "short quotient sieve")
need(10*b > 4 and 3 < D/a < 5, "pair pressure and sieve range")

# t -> log((t-a)/a) is increasing; 1/t and (b-t)/(D-t)
# are decreasing. Use a termwise upper Riemann sum.
n = 700
h = (b-2*a)/n
integral_upper = Q(0)
for i in range(n):
    t0 = 2*a+i*h
    t1 = t0+h
    z = (t1-2*a)/t1
    log_upper = 2*(sum(z**(2*j+1)/(2*j+1) for j in range(8))
                            +z**17/(17*(1-z*z)))
    integral_upper += h*log_upper*(b-t0)/(t0*(D-t0))
pair_upper = 12*integral_upper/(10*b-4)
B5=Q(1652,1000)
need(pair_upper < B5,"rank-five pair upper")

I2 = 2*(w+w**3/(3*(1-w*w)))
d=1-5*a
c=d/a
p5 = 6*d**4/(2880*a**5)*(Q(5,6)/(1+c+Q(2,5)*c*c)+Q(1,6)/(1+c))
I4 = w*(1-v-3*a)**2/(12*v*a*a*(v-2*a))
I6 = Q(10,720)*w*(1-v-3*a)**4/(4*a**4*(v-2*a)**2)
mass=I2+I4+p5+I6
need(mass<Q(3874925,10**8),"unopposed positive source")
A0=2/D
A=2/D*(1+(D/a-3)**2/4)
overlap=B5*(p5+2*(I2+I4+I6))+A0*(I2+2*I4+2*I6)+A*(I4+12*I6)
one_exit=(A0-alpha)*mass
debit=2*one_exit+overlap
need(debit<Q(349,1000),"signed full-union debit")
print(f"B5 < {float(pair_upper):.12f} < {float(B5):.3f}")
print(f"one arm {float(one_exit):.12f}; single overlap {float(overlap):.12f}")
print(f"total debit {float(debit):.12f} < .349")
