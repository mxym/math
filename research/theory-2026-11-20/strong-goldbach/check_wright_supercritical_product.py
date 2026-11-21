"""Exact rail and relative comparisons for WrightSupercriticalPrimeProduct.md."""
from fractions import Fraction as F
from itertools import product


def need(cond, description):
    if not cond:
        raise ArithmeticError(description)


amin, amax, bmin, bmax = map(F, (".508", ".513", ".501", ".506"))
delta = F(".001")
margins = []
for a,b,e in product((amin, amax), (bmin,bmax), (0,delta)):
    rails = (a-b-e, b+e-(34*a-17), b+e-(F(23,8)*a-1),
             a+b-1, b-F(".499"))
    need(all(g>0 for g in rails), 'failed corner rail')
    margins.append(rails)
minimum = tuple(min(row[i] for row in margins) for i in range(5))
need(minimum == tuple(map(F,(".001",".059",".026125",".009",".002"))), 'incorrect rails')
need(F(23,8)*F(17,33)-1 < F(".482"), 'auxiliary global rail')
need(F(".14")+F(17,33)+delta < F(".657"), 'model floor reserve')
aa,bb=F(".5125"),F(".502")
need(34*aa-17 < bb < (56*aa-17)/23, 'source-comparison witness')
print('8 exact corners and old-bound witness:', *(str(x) for x in minimum))
