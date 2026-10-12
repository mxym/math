"""Exact rational interval-bound experiment for the remaining analytic regime.
A PASS certifies only the stated scalar envelope, not the full manuscript.
All transcendental endpoint bounds use positive series with explicit tails.
"""
from fractions import Fraction as F
from math import factorial,gcd,isqrt
import json
BITS=72; SCALE=1<<BITS

def up(a):a=F(a);return F(-((-a.numerator*SCALE)//a.denominator),SCALE)
def dn(a):a=F(a);return F((a.numerator*SCALE)//a.denominator,SCALE)
def sqrtup(a):a=F(a);z=isqrt((a.numerator*(1<<100))//a.denominator);return F(z+1,1<<50)
def require(c,msg):
 if not c:raise RuntimeError(msg)
def phi(n):return sum(gcd(k,n)==1 for k in range(1,n+1))
PH=[0]+[phi(n) for n in range(1,130)]
def explr(a):
 a=F(a)
 if a<0:
  l,u=explr(-a);return dn(1/u),up(1/l)
 require(a<20,'exp range')
 n=96;S=sum((a**k/factorial(k) for k in range(n+1)),F())
 rem=a**(n+1)/factorial(n+1)/(1-a/F(n+2))
 return dn(S),up(S+rem)
def loglr(a):
 a=F(a);t=(a-1)/(a+1);N=128
 s=2*sum((t**(2*k+1)/F(2*k+1) for k in range(N)),F())
 r=2*abs(t)**(2*N+1)/((2*N+1)*(1-t*t))
 return dn(s-r),up(s+r)
def linlr(c,a,lo,hi):
 return (dn(c+a*lo),up(c+a*hi)) if a>=0 else (dn(c+a*hi),up(c+a*lo))
def endpoint(x):
 x=F(x);p=x/(1+x)
 if x==1:
  nu=(F(1,4),)*2;var=(F(1,6),)*2
  ee=explr(1)
 else:
  L=loglr((1+x)/2);z=x-1
  nu=linlr(x/z,-2*x/z**2,*L)
  var=linlr(-x*(3*x+1)/((1+x)*z*z),2*x*(x+1)/z**3,*L)

 if x==1:
  ql=dn(1/ee[1]);qu=up(1/ee[0])
 else:
  power=-2/(x-1);target=((1+x)/2)**power.numerator
  ql,qu=F(0),F(1)
  for unused in range(48):
   mid=(ql+qu)/2
   if mid**power.denominator==target:
    ql=qu=mid;break
   elif mid**power.denominator<target:ql=mid
   else:qu=mid
  require(ql**power.denominator<=target<=qu**power.denominator,'q algebraic bracket')
 A=sqrtup((1+x)*F(5,62)) # pi>31/10
 vals=[F(0)];vl=[F(0)]
 for a in range(1,65):
  P=F(1)
  for k in range(1,a):P*=2*a-k+k*x
  P/=a*a*factorial(a-1)
  vals.append(up(P*qu**a/(1+x)**(a-1)))
  vl.append(dn(P*ql**a/(1+x)**(a-1)))
 B=B1=T1=T2=F(0)
 for a in range(1,65):
  t=qu**a;H=max(2,128//a)
  sb=sb1=st1=st2=F(0)
  for h in range(1,H+1):
   w=F(PH[h],h*h)*t**(h-1)
   sb+=w;sb1+=a*h*w;st1+=a*(h-1)*w;st2+=a*a*(h-1)**2*w
  B=up(B+vals[a]*(sb+t**H/((H+1)*(1-t))))
  B1=up(B1+vals[a]*(sb1+a*t**H/(1-t)))
  T1=up(T1+vals[a]*(st1+a*t**H/(1-t)))
  T2=up(T2+vals[a]*(st2+a*a*t**H*(H/(1-t)+t/(1-t)**2)))
 t=qu**65
 B=up(B+A*F(1,768)*(1+t/(2*(1-t)))) # integral tail 2/3*64^-3/2=1/768
 B1=up(B1+A*F(1,4)/(1-t))
 T1=up(T1+A*F(1,512)*t/((1-qu)*(1-t)))
 T2=up(T2+A*F(1,8)*t/((1-qu)*(1-t)**2))
 Llow=F(0)
 if x>=1:
  r=(x-1)/(x+1)
  for a in range(1,33):
   tt=(r*ql)**a;H=max(1,32//a)
   Llow=dn(Llow+r*vl[a]*sum((F(PH[h],h*h)*tt**(h-1) for h in range(1,H+1)),F()))
 return dict(x=x,p=p,nu=nu,var=var,ql=ql,qu=qu,A=A,B=B,B1=B1,T1=T1,T2=T2,Llow=Llow)

def cf(f):return f'{f.numerator}/{f.denominator}'
def interval(a,b):
 A=endpoint(a);B=endpoint(b);a=F(a);b=F(b)
 beta,be1,T1,T2=B['B'],B['B1'],B['T1'],B['T2']
 vlow=dn(a*B['var'][0]/b);vhigh=min(F(1,4),up(b*A['var'][1]/a))
 require(vlow>=F(3,100),'variance envelope lower >=.03')
 nl,nh=A['nu'][0],B['nu'][1];pl,ph=A['p'],B['p']
 nprodhi=F(1,4) if nl<=F(1,2)<=nh else max(nl*(1-nl),nh*(1-nh))
 nprodlo=min(nl*(1-nl),nh*(1-nh))
 pvarhi=F(1,4) if pl<=F(1,2)<=ph else max(pl*(1-pl),ph*(1-ph))
 pvarlo=min(pl*(1-pl),ph*(1-ph))
 r=min(ph-nl,ph*(pl-nl)/pl)
 t0=ph/2 if a>=1 else ph
 mean=t0*beta+r*T1
 raw2=nprodhi*be1+ph*max(0,1-2*nl)*beta+max(0,pvarhi-nprodlo)*T1
 raw2+=t0*t0*beta+2*t0*r*T1+r*r*T2
 M2=up(raw2+mean*mean)
 ad=min(sqrtup(M2),2*nh*be1+mean)
 eps=F(1,500)
 shifted1=ad+eps;shifted2=M2+2*eps*ad+eps*eps
 logElow=A['Llow'] if a>=1 else -beta
 ratio=explr(up(beta-logElow))[1];invE=explr(-logElow)[1]
 Ksmall=up(F(5,4)*ratio/vlow*(F(81,10)*ph*be1+F(3,2)*shifted1+F(27,20)*shifted2))
 Kpref=up(ratio*(F(9,4)*be1+3*beta))
 C=F(3,2) if b<=1 else F(2) if b<=3 else F(4) if b<=7 else F(10)
 cc=min(F(2,3),(1+a)**2/6)
 UP=sqrtup(4*F(22,7)*(1+b))*F(1001,1000)
 Klarge=up(UP*F(7,2)*F(16,25)*8*sqrtup(vhigh/(cc*pvarlo))*C*be1/(1+a)*invE)
 Ktail=up(306*C*invE)
 total=up((Ksmall+Kpref+Klarge)/1001+Ktail/F(31031)+F(1,1000))
 require(total<1,'uniform interval positivity envelope')
 return {'a':cf(a),'b':cf(b),'total_upper':cf(total),'total_float':float(total),'Ksmall':float(Ksmall),'Kpref':float(Kpref),'Klarge':float(Klarge),'Ktail':float(Ktail),'beta':float(beta),'beta1':float(be1),'T1':float(T1),'T2':float(T2),'M2':float(M2),'ratio':float(ratio),'vlow':float(vlow),'PASS':total<1}
if __name__=='__main__':
 points=[F(i,10) for i in range(1,11)]+[F(i,4) for i in range(5,13)]+[F(i,2) for i in range(7,15)]+[F(i) for i in range(8,16)]
 require(points[0]==F(1,10) and points[-1]==15 and all(a<b for a,b in zip(points,points[1:])),'closed interval covering')
 for a,b in zip(points,points[1:]):
  print(json.dumps(interval(a,b)),flush=True)
