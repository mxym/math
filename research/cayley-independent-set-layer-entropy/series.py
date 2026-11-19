from fractions import Fraction as F
from math import comb
N=8
def add(x,y):return [x[i]+y[i] for i in range(N+1)]
def scale(x,k):return [v*k for v in x]
def mul(x,y):return [sum(x[j]*y[i-j] for j in range(i+1)) for i in range(N+1)]
def shift(x,j):return ([F(0)]*j+x)[:N+1]
def ex(x):
 if x[0]!=0:raise ValueError
 ans=[F(1)]
 for k in range(1,N+1):ans.append(sum(F(j,k)*x[j]*ans[k-j] for j in range(1,k+1)))
 return ans
z=[F(0)]*(N+1);one=[F(1)]+z[1:]
m=[z]*(N+1)
for _ in range(N+1):
 new=[z]
 for j in range(1,N+1):
  u=z
  for h in range(1,N+1):u=add(u,scale(m[h],(-1)**h*comb(j+h-1,h)))
  new.append(shift(ex(u),j))
 m=new
p=z
for j in range(1,N+1):p=add(p,scale(m[j],F((-1)**(j+1),j)))
# b=a/(1-a): lambda=b(1+b) exp(b), so b=lambda exp(-b)/(1+b), a=b/(1+b)
b=z
for _ in range(N+1):
 t=z
 for i in range(N+1):t=add(one,scale(mul(b,t),-1))
 b=shift(mul(ex(scale(b,-1)),t),1)
inv=one
for i in range(N+1):inv=add(one,scale(mul(b,inv),-1))
a=mul(b,inv)
pa=[F(0)]+[a[j]/j for j in range(1,N+1)]
print('quenched',p);print('annealed',pa);print('gap',add(pa,scale(p,-1)))
target_Q=[F(1),F(-3,2),F(23,6),F(-149,12),F(1843,40),F(-3741,20)]
target_A=target_Q[:5]+[F(-934,5)]
if p[1:7]!=target_Q or pa[1:7]!=target_A:raise ArithmeticError("sixth-order pressure check failed")
