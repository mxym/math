from fractions import Fraction as F
from math import factorial, comb
from pathlib import Path
import subprocess
import tempfile
# Use exact Python rationals; compile the companion fixed-point convolution
# into a temporary directory and collect its outward integer ceilings.
def require(ok):
 if not ok:raise ArithmeticError("explicit tiny-stop certificate failed")
with tempfile.TemporaryDirectory() as tmp:
 exe=Path(tmp)/'check'
 subprocess.run(['g++','-std=c++17','-O3',str(Path(__file__).with_suffix('.cpp')),'-o',str(exe)],check=True)
 grid=subprocess.run([str(exe)],check=True,capture_output=True,text=True).stdout.splitlines()
# Rational bounds for log, exp, and both phase Euler factors.
def loglo(u):
 v=(u-1)/(u+1)
 return 2*sum(v**(2*j+1)/(2*j+1) for j in range(24))
def expup(x,n=48):
 term=F(1);out=term
 for j in range(1,n+1):
  term*=x/j;out+=term
 return out+term*x/(n+1-x)
def require_euler_bounds():
 pi_lo,pi_hi=F(3141592653589,10**12),F(3141592653590,10**12)
 top=2*pi_hi
 j1=lambda x:x-x**3/72+x**5/9600
 require(j1(top)+1/(2*pi_lo)-4/pi_hi*loglo(2*pi_lo)<loglo(F(6)))
 for i in range(100,629):
  x,y=F(i,100),F(i+1,100)
  require(expup(j1(y))**7 < 6**7*x**9)
 # sqrt exp J2=exp(gamma+log x-Ci(x)); use |Ci(x)|<=2/x.
 require(expup(F(578,1000)+1)<5 and expup(F(578,1000)+F(1,10))<2)
 require(expup(F(3,10))<F(135,100))
 require(expup(F(9,200))/192<F(75,1000)**2)
require_euler_bounds()
b=F(1,250)
c=F(9,2)*b
d=c+F(1,1000000)
w=6*b
pi=F(3141592653589,10**12)
S=10**12

def Q(n,d): return F(n,d)
def add(p,q): return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))]
def mul(p,q):
 z=[F(0)]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):z[i+j]+=x*y
 return z
def scale(p,k): return [x*k for x in p]
def power(p,k):
 z=[F(1)]
 for _ in range(k):z=mul(z,p)
 return z
def deriv(p,k): return [F(p[i])*factorial(i)/factorial(i-k) for i in range(k,len(p))] or [F(0)]
def val(p,x):
 a=F(0)
 for c0 in p[::-1]:a=a*x+c0
 return a
def integral(p):return sum(F(x,i+1) for i,x in enumerate(p))
def ubnorm(p):
 n=len(p)-1
 return max(abs(sum(F(p[i])*comb(k,i)/comb(n,i) for i in range(k+1))) for k in range(n+1))
def L1(p,n=512):
 return sum(abs(val(p,F(2*i+1,2*n))) for i in range(n))/n+ubnorm(deriv(p,1))/(4*n)
def root(x,n):
 num=x.numerator*S**n;den=x.denominator;l,h=0,1
 while h**n*den<num:h*=2
 while h-l>1:
  m=(l+h)//2
  if m**n*den>=num:h=m
  else:l=m
 return F(h,S)
def pf(x): return add(scale(power(x,4),44),scale(power(x,6),-112))
cc=[1,1,-39,-192,-376,-336,-112]
ext=F(3)
neg0=[sum(F(cc[i])*ext**i*comb(4+j-i,j-i) for i in range(j+1)) for j in range(5)]
neg=mul(power([1,-1],5),neg0)
pos=pf([F(1,2),F(-1,2)])
taper=[1,0,0,0,-35,84,-70,20] # 1 - cumulative Beta(4,4)
e0=pf([0,d])
e1=mul(pf([d,w]),taper)
def moment(p,q,l,h,k):
 return (l*L1(deriv(p,k))/l**k+h*L1(deriv(q,k))/h**k)
S0=[moment(neg,pos,ext,F(1,2),k) for k in range(6)]
S0[5]+=1056
E0=[moment(e0,e1,d,w,k) for k in range(6)]
E0[5]+=abs(val(deriv(e0,4),0)/d**4)+abs(val(deriv(e0,4),1)/d**4-val(deriv(e1,4),0)/w**4)+abs(val(deriv(e1,4),1)/w**4)
def U(x):return min(v/x**k for k,v in enumerate(S0))+min(v/x**k for k,v in enumerate(E0))
# endpoint jumps of actual Fdelta on [-3,0], [0,.5-d-w], [.5-d-w,.5-d].
c0=F(1,2)-d-w
pseg=[(-ext,F(0),neg,True),(F(0),c0,pf([F(1,2),-c0]),False),(c0,F(1,2)-d,[F(0)],False)]
# taper cumulative Beta(4,4) in z=(d+w-t)/w, equals beta(1-v)=1-beta(v).
pseg[-1]=(c0,F(1,2)-d,mul(pf([d+w,-w]),taper),False)
J=[{} for _ in range(15)]
for l,r,p,rev in pseg:
 a=r-l
 for k in range(len(p)):
  j=J[k]
  if rev:
   L=val(deriv(p,k),1)/(-a)**k;R=val(deriv(p,k),0)/(-a)**k
  else:
   L=val(deriv(p,k),0)/a**k;R=val(deriv(p,k),1)/a**k
  j[l]=j.get(l,F(0))+L;j[r]=j.get(r,F(0))-R
require(all(not any(j.values()) for j in J[:4]))
C5=sum(sum(map(abs,j.values()))/(40/b)**(k-4) for k,j in enumerate(J) if k>=4)
MD=(d*integral(e0)+w*integral(e1))/b**2
# 1/z <= 1/d on taper portion; direct integrate e0/z exactly.
UD=2/b*(integral(e0[1:])+w*integral(e1)/d)+F(2,3)*MD
base=1-c-b
S1=F(0);S2=F(0)
last=0
for row in grid:
 tl,tr,R1,R2,*_=map(int,row.split())
 require(tl==last and tr>tl and R1>0 and R2>0)
 last=tr
 if tl<300: continue
 x=F(tl,1000)/b;y=F(tr,1000)/b
 eo=6*root(y**9,7)
 eb=2*y
 ub=U(x)
 S1+=2/pi/base*ub*eo*F(R1,10**8)*(y-x)
 S2+=2/pi/root(base,2)*ub*eb*root(F(R2,10**8),2)*(y-x)
require(last==40000)
# note: fix the 1/sqrt(base) outward rounding (never divide by sqrt-up)
sbase=1/root(1/base,2)
S2*=root(base,2)/sbase
# 0 <= tau <= .3; e^.3<1.35, r1<=1.35 tau^5/120; sqrt(V)<=.075 tau^5.
# ξ <= 1: norm at zero and exact monomial weights.
lo1=2/pi/base*F(135,100*120)*b**5*(
  (S0[0]+E0[0])*6/6
  + 6*(S0[5]*(root((F(3,10)/b)**16,7)-1)*F(7,16)
       + E0[0]*(root((F(3,10)/b)**51,7)-1)*F(7,51)))
# sqrt exp J₂ <= 2ξ for ξ>=10; <= 5 max(1,ξ) for ξ>=1 and <10; <=2 otherwise.
X=F(3,10)/b
lo2=2/pi/sbase*F(75,1000)*b**5*(
 (S0[0]+E0[0])/3 +
 5*(S0[5]*F(399,2)+E0[0]*(20**7-1)/7) +
 2*(S0[5]*(X**2-400)/2+E0[0]*(X**7-20**7)/7))
# High τ >=40: R1<=4 e^{J1(τ)}/(κ-1), all J1 upper 6 ξ^(9/7).
hi1=2/pi/base*C5*F(144,1)/F(7,2)*root(b**19,7)*F(7,10)*root(F(1,40)**10,7)
# V<=32 exp(J2(τ))*sqrt τ/(κ-1), sqrt exp J2 <= 2τ, similarly unmarked.
hi2=2/pi/sbase*C5*4*root(F(64,7),2)*b**3*F(4,7)*root(F(1,40)**7,4)
for k,v in [('MD',MD),('UD',UD),('C5',C5),('R finite',S1),('R low',lo1),('R tail',hi1),('Xsqrt finite',S2),('Xsqrt lo',lo2),('Xsqrt hi',hi2)]: print(k,float(v),flush=True)
r=S1+lo1+hi1; x=S2+lo2+hi2
budget=2*F(4298,1000)*(MD+r)+2*F(301,1000)*F(1701,100000)+F(300,1000)**2+(MD+2*r)*UD+F(4,5)/b*x*x+F(1,10000)
require(MD<F(15765,10**6) and UD<F(17632,10**6))
require(r<F(1982,100000) and x<F(4193,100000))
require(budget<F(76,100))
print('total debit strictly below .760:',float(budget))
