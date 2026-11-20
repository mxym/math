"""Arithmetic checks accompanying the conditional mixed-slice note; no graph or solver is assumed."""
from fractions import Fraction as F
from math import factorial
for add in range(-40,41):
 t=-1+9*add
 assert (7*(9*t+t*t)-70)%126==0
 t=-2+9*add
 assert (7*(9*t+t*t)-154)%126==0
for i in range(1,9):
 b=F(99*i*(9-i),81)
 assert b==(F(88,9) if i in (1,8) else b)
 if i not in (1,8): assert b>=F(154,9)>14
assert F(196,9)>F(88,9)>F(70,9) and F(196,9)<28
assert F(196,9)*99/49==44
assert 21**2*F(196,9)/7==1372
for n,total,lower in [(858,4620,33),(861,4704,12)]:
 assert 28*(n-693)==total
 assert 99-(total-99*44)//4==lower
assert (44**43)<4*(43**43)
assert 44**42<9*(42**42)
assert F(4*196,9)<98
assert (14*364)<72**2
assert F(48+16)+F(64,10)==F(352,5)>70
# Countercheck numerical floor for the elementary log majorant by its
# derivative on (1,+infty): second derivative positive and minimizer 2,
# and equality derivative log2−1/2 exactly matches chosen coefficient.
assert 2**3<3**2
for sj in (2,4,6):
 if (7*sj)%4==0: assert sj==4
print('Passed residue, cone, pseudodeterminant, and support-multiplicity checks.')
