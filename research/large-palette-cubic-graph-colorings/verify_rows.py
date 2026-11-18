"""Exact uniform end-point tests, including denominators; no floating point."""
from fractions import Fraction as F
rows=[(37,5,[[0,0,0,0,F(1,5),-1,-F(104,7),-F(778,7),-F(3509,6)],[0,0,0,1,1,-F(94,9),-F(727,6),-F(1960,3),-F(7895,2)]]),(88,6,[[0,0,0,0,0,F(1,6),0,-F(25,2),-F(255,2)],[0,0,1,2,F(7,2),6,-F(113,3),-702,-F(20481,4)],[0,0,0,0,1,4,0,-40,-F(1847,6)]])]
for q,g,rs in rows:
 z=F(1,q);tail=2*(7*z)**9/(9*(1-7*z))/z**(g-1)
 def val(r):
  d=next(i for i,v in enumerate(r) if v)
  return r[d]+sum(min(0,v)*z**(k-d) for k,v in enumerate(r) if k>d)
 slack=val(rs[0])-tail
 if not (slack>0 and all(val(r)>0 for r in rs[1:])):
  raise ArithmeticError("non-positive endpoint margin or auxiliary row")
 print('q',q,'U-z_scaled_tail',slack,'short rows',[str(val(r)) for r in rs[1:]])
