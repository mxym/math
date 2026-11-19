from math import factorial as F,comb
from fractions import Fraction as Q
def H(r,s):return sum((Q(1,k**s) for k in range(1,r+1)),Q(0))
def J(i,j):
 # R=2/3 * (r+1)(r+2)(r+3) / prod(r+i+l)(r+j+l); poles at -q
 from collections import Counter
 D=Counter([l+i for l in (1,2,3)]+[l+j for l in (1,2,3)])
 D.subtract((1,2,3))
 # compute order 1 and 2 coefficients by product and logarithmic derivative
 F1=Q(0); F2=Q(0); cancels=Q(0)
 for q,c in D.items():
  if c<=0:continue
  v=Q(2,3); diff=Q(0)
  for h,a in D.items():
   if h==q or a==0:continue
   v*=Q(h-q)**(-a);diff-=Q(a,h-q)
  A=v if c==1 else v*diff
  B=v if c==2 else 0
  F1-=A*H(q-1,1)+B*H(q-1,2);F2+=B;cancels+=A
 if cancels:raise ValueError()
 return F1,F2
a,b=Q(1),Q(0)
for i in range(5):
 for j in range(5-i):
  m=4-i-j
  coef=81*Q(F(4),F(i)*F(m)*F(j))*2**m*Q(F(2*j+m)*F(2*i+m),F(9))
  rat,zeta=J(i,j);a+=coef*rat;b+=coef*zeta
print('c=',a,'+',b,'zeta(2)')
print(float(a)+float(b)*3.141592653589793**2/6)
if (a,b)!=(Q(9,4),Q(18,35)):raise ArithmeticError('constant disagreement')
