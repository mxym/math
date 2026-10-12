"""Exact scalar/base certificates. Analytic tail reductions are in the proof notes.
Not a complete real-rootedness verifier.
"""
from fractions import Fraction as F
from math import prod, factorial, gcd
import json
q=F(53,200); x=F(1,10); N=64; HH=16

def require(c,msg):
 if not c: raise RuntimeError(msg)
def phi(h):return sum(gcd(k,h)==1 for k in range(1,h+1))
def P(a):return prod((2*a-k+k*x for k in range(1,a)),start=F(1))/(a*a*factorial(a-1))
v=[F(0)]+[P(a)*q**a/(1+x)**(a-1) for a in range(1,N+1)]
require(q**9>F(11,20)**20,'critical q upper')
B=B1=F(0)
for a in range(1,N+1):
 t=q**a
 B+=v[a]*(sum((F(phi(h),h*h)*t**(h-1) for h in range(1,HH+1)),F())+t**HH/(17*(1-t)))
 B1+=a*v[a]*(sum((F(phi(h),h)*t**(h-1) for h in range(1,HH+1)),F())+t**HH/(1-t))
t=q**(N+1)
B+=F(1,2560)*(1+t/(2*(1-t)))
B1+=F(3,40)/(1-t)
require(B<F(2,5),'beta<2/5')
require(B1<F(4,5),'beta1<4/5')
T1=q*q/(1-q)+F(9,80)*q*q/((1-q)*(1-q*q))
T2=q*q/(1-q)**2+F(9,40)*q*q/((1-q)*(1-q*q)**2)
require(T1<F(3,25),'T1<3/25')
require(T2<F(1,5),'T2<1/5')
b=[F(0)]*24
for n in range(1,24):
 b[n]=sum((F(phi(h),h*h)*v[n//h]*q**(n-n//h) for h in range(1,n+1) if n%h==0),F())
for n in range(1,16):require(b[n]**2*n**5<F(4,25),'b finite base')
require(F(9,10)*64*F(4,15)**8<F(1,10),'b tail at16')
hh=[F(1)]+[F(0)]*23
for n in range(1,24):
 hh[n]=sum((k*b[k]*hh[n-k] for k in range(1,n+1)),F())/n
 require(hh[n]**2*n**5<1,'h finite base')
# exp(2/5)<3/2 by a positive Taylor sum plus a geometric upper tail.
z=F(2,5);cut=12
expupper=sum((z**k/factorial(k) for k in range(cut+1)),F())+(z**(cut+1)/factorial(cut+1))/(1-z/F(cut+2))
require(expupper<F(3,2),'exp beta bound')
require(F(6)*F(4,5)/24+F(2,5)*F(3,2)*(1+9*F(4,5)/24)<1,'h induction at24')
# Further rational residuals in SMALL_SADDLE_POSITIVITY.md.
tlog=F(9,31)
Llower=2*sum((tlog**(2*k+1)/F(2*k+1) for k in range(9)),F())
require(-F(10,9)+F(200,81)*Llower>F(9,25),'nu/x lower')
require(F(512,343)/(1-F(16,7007))<F(25,16),'A<5/4 squared')
require(F(9,4)**2>F(9,4)*F(8,7)**5,'prefactor derivative')
require(25*F(22,7)**5<8192,'C2 Gaussian constant')
require(F(22,7)**9*F(4,3)**5<131072,'A1 V>=1 constant')
require(F(35000)*1001**3*F(3,8)**50<1,'periodic error')
require(F(912,1001)+F(567,31031)+F(1,1000)<1,'final small-saddle margin')
out={'status':'PASS','scope':'small-x scalar and finite-base certificates only; analytic reductions required','q_upper':'53/200','beta_upper':'2/5','beta1_upper':'4/5','T1_upper':'3/25','T2_upper':'1/5','b_global_constant':'2/5 with analytic n>=16 tail','h_global_constant':'1 with analytic n>=24 recurrence','finite_h_max_diagnostic':max(float(hh[n])*n**2.5 for n in range(1,24))}
print(json.dumps(out,indent=2))
