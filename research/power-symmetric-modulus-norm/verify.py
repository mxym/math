"""Exact characteristic-polynomial and finite-witness checks; fail closed under -O."""
from fractions import Fraction as Q
def ck(pred,desc):
 if not pred: raise ArithmeticError(desc)
def t(a):return tuple(map(tuple,zip(*a)))
def m(a,b):return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in t(b)) for row in a)
def lin(a,b,fac=1):return tuple(tuple(fac*(x+y) for x,y in zip(l,r)) for l,r in zip(a,b))
def sm(c,a):return tuple(tuple(c*x for x in r) for r in a)
def block(a,b):
 z=((0,0),(0,0))
 return tuple(z[i]+a[i] for i in range(2))+tuple(b[i]+z[i] for i in range(2))
def bd(a,b):
 z=((0,0),(0,0))
 return tuple(a[i]+z[i] for i in range(2))+tuple(z[i]+b[i] for i in range(2))
def check_root(x,r):
 g=m(t(x),x)
 ck(m(r,r)==g,'wrong square root')
 # All proposed roots below are block diagonal symmetric with 2x2 PSD blocks.
 for i in (0,2):
  a,b=r[i][i:i+2];c,d=r[i+1][i:i+2]
  ck(b==c and min(a,d)>=0 and a*d-b*c>=0,'indefinite square root')
def sing_p1():
 A=((8,4),(4,2)); C=((-8,4),(4,-2)); B=((0,0),(0,21)); M=lin(A,C,Q(1,2))
 tops=[]
 for Z,H in ((A,A),(C,sm(-1,C)),(M,((4,0),(0,4)))):
  X=block(Z,B); r=bd(B,H);s=bd(H,B)
  check_root(X,r); check_root(t(X),s)
  S=lin(r,s,Q(1,2));a,b=S[0][:2];c,d=S[1][:2]
  tr=a+d;det=a*d-b*c
  top = Q(25,2) if Z==M else Q(12)
  ck(top**2-tr*top+det==0 and top>=tr-top,'incorrect top eigenvalue')
  ck(S==bd((S[0][:2],S[1][:2]),(S[0][:2],S[1][:2])),'asymmetric copy')
  tops.append(top)
 ck(tops[2]>(tops[0]+tops[1])/2,'no gap')
 print('p=1 integer 4x4: both actual PSD square roots verified for both endpoints and midpoint; operator norms',*[str(a) for a in tops])
def low():
 # p=3/2; s=2^(-4). Compare (cs)^p with 2s^2 using their fourth powers.
 s=Q(1,16); ss=s*s;cc=1-ss
 ck((ss*cc)**3>(2*ss)**4,'midpoint endpoint gap p=3/2')
 # characteristic polynomial of 2P+uu^T at h=2+2s^2, beyond its midpoint 3/2.
 h=2+2*ss; ck(h*h-3*h+2*cc==4*ss*ss and h>Q(3,2),'upper root bound')
 print('p=3/2: s=1/16; exact fourth-power and characteristic-polynomial certificates')
def high():
 # p=3; T=2^(5/(3-2)). Test eigenpair and bound with no real-powers arithmetic.
 T=Q(32);A=((T-1/T,1),(1,0))
 ck(m(A,((T,),(1,)))==((T*T,),(T,)),'wrong eigenpair')
 gap=(T/2)**3/(T*T+1)
 ck(gap==4*T*T/(T*T+1)>2,'gap p=3')
 print('p=3: T=32; exact Rayleigh gain above T^3 is at least',gap)
if __name__=='__main__':
 sing_p1();low();high();print('PASS')
