"""Exact rail, free-exponent, and reciprocal marker-count checks."""
from fractions import Fraction as F
from itertools import product
from math import comb


def need(cond, description):
    if not cond:
        raise ArithmeticError(description)


S = tuple(map(F,(".123", ".125")))
P = tuple(map(F,(".491", ".492")))
R = tuple(map(F,(".5095", ".5105")))
I = tuple(map(F,(".02098", ".02102")))
D = F(".001")
ran = []
for s,p,r,w,e in product(S,P,R,I,(F(0),D)):
    long = p+w
    rails = (long-r-e, r+e-(34*long-17), r+e-(F(23,8)*long-1),
             p+r-1, r-p, 1-long-F(3,8))
    need(all(g>0 for g in rails), 'dispersion, supercriticality or orientation')
    ran.append(rails)
for k in range(18):
    g = sum((F((-1)**j * comb(k,j), j+1) for j in range(k+1)), F(0))
    need(g == F(1,k+1), 'binomial reciprocal coefficient')
    need((k+1)*g == 1, 'at-least-one identity')
umin,umax = 1-S[1]-P[1],1-S[0]-P[0]
need((umin,umax)==tuple(map(F,(".383",".386"))), 'u range')
need(19*I[0]>umax and 18*I[0]>umax-I[0], 'marker rank')
free = umin-18*I[1]-D
need(free == F(".00364"), 'free-k exponent')
print('32 exact range corners, 18 reciprocal counts; rail minima',
      *(str(min(row[i] for row in ran)) for i in range(6)))
print('free k exponent:', free)
