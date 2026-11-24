"""Exact physical four-coclique and cubic-trace filter after the integer filtration."""
from fractions import Fraction as F
from math import ceil,isqrt
from cost21_integer_filtration import model

def root_bounds(v):
 # Rational enclosures of sqrt(v) of width 1/10^5; no numerical tolerances.
 scale=10**5
 v=F(v);r=isqrt((v*scale**2).numerator//(v*scale**2).denominator)
 return F(r,scale),F(r+1,scale)

def walk4(m,e,l):
 # Strip l actual eigenvalues 2 and one Perron eigenvalue not among them.
 B=F(2*e+4*m-16*l);L=max(F(4),2+F(2*e,m));z=L*L
 if z>B:return False
 v=B-z
 u0=(z-4*L)**2+16*v+8*v*root_bounds(v)[1]+v*v
 u1=B*B+16*B-8*B*root_bounds(B)[0]
 j,rem=divmod(2*e,m);Q=(m-rem)*j*j+rem*(j+1)**2
 return max(u0,u1)>=2*Q-18*e+16*m

def verify():
 rows,u125=model()
 d=lambda n:ceil(F(24*(n-1),n+24))
 stage=[0]*5;old=[0]*5;new=[0]*5; controls=[]; final=[];details=set()
 for r in range(9,14):
  for f in range(4):
   for n in range(46,66):
    for m in range(82):
     for s in range(56):
      q=24*(n-88)+92*r-208*f-8*m-12*s
      if not 0<=q<=600:continue
      target=(1,r,f,m,s,q,0,0)
      E=720-18*r+50*f-16*m+2*s+3*q//2
      lo,hi=0,E
      if hi<lo:continue
      for coeff in rows:
       z=sum(x*y for x,y in zip(coeff[:6],target))
       v=coeff[7]
       if v>0:lo=max(lo,-(z//v))
       elif v<0:hi=min(hi,z//(-v))
       elif z<0:break
       if lo>hi:break
      else:
       stage[r-9]+=1;assert f==0
       amount=sum(x*y for x,y in zip(u125,target))
       was=now=last=False
       for b in range(18,n//2+1):
        a=n-b
        if 72*(a-b)>amount:continue
        c=42-d(a)-d(b);l=m-c
        assert l>0 and c>1
        # The least allowable y maximizes the set of possible edge counts at each stage.
        for e in range(E-lo+1):
         small=3*l<=min(m,e) and 4*m*l<=2*e*c
         big=(3*(l+1)<=e and 4*e*e*c+8*e*l*m+4*l*(m-1)*m*m<=2*e*(c-1)*m*m)
         if not(small or big):continue
         was=True
         k=max(0,(2*e-E+lo+5)//6)
         if 6*k>e:continue
         B=2*e+4*m-16*l
         z=24*k+12*e+8*m-64*l
         if B<0 or (z>0 and z*z>B**3):continue
         now=True
         if 2*e+lo>E or not walk4(m,e,l):continue
         last=True;details.add((r,n,m,s,q,a,b,c,e))
       old[r-9]+=was;new[r-9]+=now
       if now:controls.append((r,n,m,s,q))
       if last:final.append((r,n,m,s,q))
 assert stage==[0,5,12,19,5] and old==[0,5,8,4,0] and new==[0,5,3,0,0]
 assert controls==[(10,59,27,0,8),(10,59,28,0,0),(10,60,28,0,24),(10,60,28,1,12),(10,60,28,2,0),(11,56,28,1,8),(11,57,29,1,24),(11,58,29,3,24)]
 assert final==[(10,59,27,0,8)]
 assert details=={(10,59,27,0,8,a,b,16,e)for a,b in [(33,26),(30,29)]for e in range(55,61)}
 print(stage,old,new,final);print("signed splits and edge counts:",sorted((a,b,e)for r,n,m,s,q,a,b,c,e in details))
if __name__=='__main__':verify()
