from fractions import Fraction as F
j = 2*(F(1,6)+F(1,6)**3/3)-F(160,1000)+F(192,10000)
log7 = 2*(F(3,4)+F(3,4)**3/3)
new = F(86,267)*j*log7*F(2,5)
if not (j > 0 and new > F(44,1000)):
    raise ArithmeticError((j,new))
print('Exact lower for new dyadic positive packet:', new, float(new))
