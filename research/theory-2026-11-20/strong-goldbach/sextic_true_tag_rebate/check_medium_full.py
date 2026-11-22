from fractions import Fraction as F
from math import isqrt, comb, ceil
def require(k):
 if not k:raise ArithmeticError("sextic medium certificate failed")
S=10**12
J=[[S]*7001]
for j in range(2,9):
 row=[0]*7001
 for h in range(1001,7001):
  row[h]=row[h-1]+(J[-1][h-1000]+h-2)//(h-1)
 J.append(row)
def loglo(x):
 q=(x-1)/(x+1)
 return 2*sum(q**(2*j+1)/(2*j+1) for j in range(10))
def sqrt(x,k):
 n,d=x.numerator,x.denominator
 p=isqrt(n*S*S//d)
 return F(p+(k and p*p*d!=n*S*S),S)
def w3(u,v):
 cs=[-78,1152,-4512,6720,-3360]
 return -sum(vv*sum(F(comb(k,j),(j+1)*(k-j+1))*u**j*v**(k-j) for j in range(k+1)) for k,vv in enumerate(cs))
def C5(q):
 hi=sqrt(q,True)
 return 10080*hi-1056/hi
def round_down(v):
 return F(v.numerator*S//v.denominator,S)
def round_up(v):
 return F(ceil(v*S),S)
def same():
 den=1000
 n=p=U=m3=m4=m5=0
 smax=F(".065")
 for i in range(5,130):
  for j in range(i+1,131):
   u,v=F(i+1,den),F(j+1,den)
   ul,vl=F(i,den),F(j,den)
   if u+v>smax:continue
   area=F(1,10**6)
   D=F(".555")-u-v
   T=1-u-v; Tp=1-ul-vl
   z=D/3
   require(F(".1325")<z<F(".187") and v<z)
   ix=ceil((Tp/z-1)*1000)
   raw=2*loglo(F(2))/D-F("3.446")*sum(F(row[ix],S) for row in J[3:])/T
   require(raw>0)
   q0=ul**2+vl**2
   q4=q0+T*T/2
   q5=q0+T*T/3
   low3=w3(u,v)
   low4=(1680*q4-528)*z*(T-z)
   low5=(40320*sqrt(q5/24,False)-1056*sqrt(2/q5,True))*z*z*(T-2*z)
   pl=min(low3,low4,low5)
   require(pl>0)
   p+=round_down(area*pl*raw)
   n+=1
   A4=1680*(u*u+v*v+Tp*Tp)-528
   low=z*(T-z);high=Tp*Tp/4
   Z=min(high,max(low,A4/6720))
   up3=w3(ul,vl)
   up4=Z*(A4-3360*Z)
   up5=C5(u*u+v*v+(Tp-2*z)**2+2*z*z)*Tp**3/27
   R3=up3/T
   R4=(Tp/2-z)*A4-3360*(T*(Tp**2/4-z*z)/2-((Tp/2)**3-z**3)/3)
   t=Tp-3*z
   R5=C5(u*u+v*v+3*z*z+2*z*t+t*t/2)*t*t/12
   require(min(up3,up4,up5,R3,R4,R5)>0)
   require(A4-3360*(Tp**2/4)>0)
   m3+=round_up(area*R3);m4+=round_up(area*R4);m5+=round_up(area*R5)
   D0=F(".499")-u-v
   require(2<D0/z<=3)
   U+=round_up(area*max(up3,up4,up5)*2/D0)
 m=m3+m4+m5
 loss=2*((1+F(".228")+F(".007445"))*m-p
         +min(F(".852")*m,F(".01701")*U)+F(".009042")*U)+m*U
 print('sum cap',smax,'cells',n,'prime lower',float(p),'ordinary upper',float(m),
       'ranks',*(float(v) for v in [m3,m4,m5]),'receiver upper',float(U),'debit upper',float(loss))
 print('integer ceilings/floor at 10^12',int(p*S),int(m*S),int(U*S))
 require(n==729 and p>F(".05846") and m<F(".16921") and U<F(".52844"))
 require(loss<F(".419"))
 return n,p,m,U,loss
if __name__=='__main__':
 same()
