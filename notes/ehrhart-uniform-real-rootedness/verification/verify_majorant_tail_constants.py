"""Exact finite bases and residual inequalities for the proved tail induction."""
from verify_large_x_intervals import F,up,endpoint,PH,require,explr
from math import factorial
import json
rows=[(F(1),F(41,100),F(3,8),F(1,2),F(7,12),F(6,5),F(9,5),F(3,2)),
(F(3),F(4,7),F(1,2),F(3,5),F(81,100),F(7,4),F(9,4),F(2)),
(F(7),F(81,100),F(16,25),F(5,6),F(9,8),F(8,3),F(25,8),F(4)),
(F(15),F(8,7),F(3,4),F(4,3),F(3,2),F(4),F(9,2),F(10))]
for x,A,qcap,B,beta,beta1,emass,C in rows:
 e=endpoint(x);q=e['qu']
 require(q<=qcap,'q cap')
 require(A*A>(1+x)*F(5,62),'primitive A')
 require(qcap<A,'primitive n1')
 require(e['B']<beta and e['B1']<beta1,'mass/moment caps')
 require(explr(beta)[1]<emass,'exponential cap')
 require(A+3*A*512*qcap**32<B,'log tail n64')
 v=[F(0)]
 for a in range(1,128):
  P=F(1)
  for k in range(1,a):P*=2*a-k+k*x
  P/=a*a*factorial(a-1)
  v.append(up(P*q**a/(1+x)**(a-1)))
 b=[F(0)]*128;h=[F(1)]+[F(0)]*127
 for n in range(1,128):
  b[n]=up(sum((F(PH[t],t*t)*v[n//t]*q**(n-n//t) for t in range(1,n+1) if n%t==0),F()))
  h[n]=up(sum((k*b[k]*h[n-k] for k in range(1,n+1)),F())/n)
  if n>=64:require(h[n]**2*n**5<C*C,'tail finite base')
 require(6*beta1*C/128+B*emass*(1+9*beta1/128)<C,'tail induction')
 print(json.dumps({'x':str(x),'C':str(C),'status':'PASS','base':'64..127','induction':'s>=128','B':str(B),'beta':str(beta),'beta1':str(beta1)}),flush=True)
