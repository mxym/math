from higher_moments import rows, projections, SHIFTS, GRAM, dot,times
from fractions import Fraction as F
from math import isqrt,lcm
from functools import cache
from collections import defaultdict,Counter
import sympy as sm
illegal={(0,16),(0,20),(0,26),(1,21),(1,25),(2,26),(2,28),(2,30),(3,37)}
def folded(a,t,delta):
 k=(a+4)//9
 return a-9*k,t-22*a*k+99*k*k,delta-22*k
def basic(a,t):
 return t>=11*abs(a) and (t-a)%2==0 and not(abs(a)==0 and 0<t<14) and not(abs(a)==1 and t<=19) and (abs(a),t) not in illegal and not(abs(a)==2 and t==24)
def move(z,n):
 a,t,d=z
 return folded(a+2*n,t+22*n*n+2*n*d,d+22*n)
def negz(z):return -z[0],z[1],-z[2]
def okeys(z):
 zs=[move(z,n) for n in range(-14,15)]
 return zs+[negz(u)for u in zs]
def orb(z):
 o=okeys(z);a,t,d=min(o,key=lambda z:(9*z[1]-11*z[0]*z[0],z[0],z[2]))
 return a,t,d
def getkeys(keys):
 out={};by=defaultdict(list)
 for a,t in keys:
  if not basic(a,t):continue
  for d in range(-isqrt(22*t),isqrt(22*t)+1):
   if (a,t)==(0,18) and d!=0: continue
   if (a,t)==(1,27) and d not in (-3,4):continue
   if (d-4*a)%7 or (9*d-22*a)**2>154*(9*t-11*a*a):continue
   o=orb((a,t,d))
   if o not in out:out[o]=all(basic(*move(o,j)[:2])for j in range(-6,7))
   if out[o]:by[a,t].append((d,o))
 return sorted(o for o,x in out.items()if x),by
def buildcore():
 allray=[]
 for row in rows():
  z=dict(row)
  for t,s,n in [((1,25),(0,16),8),((1,27),(0,18),9),((1,27),(2,26),2),((0,26),(1,21),8)]:z[s]=z.get(s,0)-n*row.get(t,0)
  allray.append(z)
 keys=sorted(set().union(*allray,*(projections(sh,n).keys()for sh in [None,*SHIFTS]for n in [1,2,3])));os,by=getkeys(keys);ix={o:i for i,o in enumerate(os)}
 def zrow(r):
  h=[0]*len(os)
  for k,v in r.items():
   for d,o in by.get(k,[]):h[ix[o]]+=v
  return h
 m=[zrow(r)for r in allray];b=[0]*len(m)
 for key,rhs in [((0,0),1)]:
  m.append(zrow({key:1}));b.append(rhs)
 return os,ix,by,m,b,zrow
@cache
def harmonic_formula(d):
 from fractions import Fraction
 cs=[Fraction(1)]
 for j in range(d//2):
  cs.append(-cs[-1]*Fraction((d-2*j)*(d-2*j-1),2*(j+1)*(48+2*d-2*j-4)))
 den=lcm(*(c.denominator for c in cs));return [int(x*den)for x in cs]
@cache
def harmonic(d,ip,v2,z2):
 co=harmonic_formula(d)
 return sum(c*ip**(d-2*j)*(v2*z2)**j for j,c in enumerate(co))
def cumul(shift,n,table,h,sd,by,ix,d):
 scale=1 if shift is None else 3;N=len(ix);vec=[0]*N
 v2=9702*sd*sd+9*dot(h,times(GRAM,h))
 for (a,t),ws in table.items():
  if not by.get((a,t)):continue
  wg=Counter((3//scale)*dot(x,h)for x in ws)
  for delt,o in by[a,t]:
   ip=(9*delt-22*a)*sd
   w=sum(nw*harmonic(d,ip+k,v2,2*n)for k,nw in wg.items())
   vec[ix[o]]+=w*(2 if a else 1)
 return vec
def moments(by,ix,degree,directions):
 shifts=[None,*SHIFTS];out=[]
 for sh in shifts:
  tab=[projections(sh,j)for j in [1,2,3]]
  for h,sd in directions:
   for d in degree:
    s1,s2,s3=[cumul(sh,n,k,h,sd,by,ix,d) for n,k in enumerate(tab,1)]
    if d==2:out.append([v+48*u for u,v in zip(s1,s2)]);out.append([w+195804*u for u,w in zip(s1,s3)])
    else:
     c1,c2={4:(151740,192),6:(-99180,-552),8:(50220,432),10:(-22140,-312),14:(-2700,-72)}[d]
     out.append([w-c1*u-c2*v for u,v,w in zip(s1,s2,s3)])
 return out


def main():
 os,ix,by,m,b,rr=buildcore()
 assert (len(os),sum(map(len,by.values())))==(116,191)
 def sel(k,d):
  return [int(z==dict(by[k])[d])for z in os] if d in dict(by[k])else [0]*len(os)
 m.append(rr({(1,27):1,(0,18):-9}));b.append(0)
 m.append(sel((2,22),22));b.append(1)
 m.append(rr({(0,14):1}));b.append(0)
 m.append(sel((2,22),15));b.append(0)
 dirs=[((0,0,0,0),1),((1,2,3,1),1),((1,-1,1,-2),1),((2,-1,1,2),1)]
 for d in (2,4,6,8):
  q=moments(by,ix,[d],dirs);m+=q;b += [0]*len(q)
 # 3V + 320M +62W123 = 8004. V includes 3*K123,4, before subtracting 3*77.
 terms=[((4,46),2,3),((2,22),8,6),((2,34),8,6),((2,34),1,9),
        ((1,23),11,24),((1,29),11,6),((1,23),4,9)]
 target=[sum(z*sel(k,p)[i]for k,p,z in terms)+320*rr({(2,22):1})[i]
         +62*rr({(1,23):1})[i]for i in range(len(os))]+[8004]
 table=[r+[s]for r,s in zip(m,b)]
 a,piv=sm.Matrix(table).to_DM().rref();a=a.to_Matrix().tolist()
 assert len(piv)==105 and len(os) not in piv
 for i,j in enumerate(piv):
  coeff=target[j]
  if coeff:target=[s-coeff*t for s,t in zip(target,a[i])]
 assert not any(target)
 print('116 orbits, 191 signed positive-charge angle slots; exact rank 105; identity verified')
 old=[];surv=[]
 for M in (1,3):
  for S in range(22):
   n,rem=divmod(291+5*M+2*S,6);k=189-42*M-9*S
   if rem or k<0:continue
   old.append((M,S,n,k))
   threeV=1173-320*M-62*S
   if threeV<0:continue
   if M==3 and threeV<2*k:continue  # Sum of the three V_C equals threeV.
   surv.append((M,S,n,k))
 assert len(old)==8
 assert surv==[(1,2,50,129),(1,5,51,102),(1,8,52,75),(1,11,53,48),(3,0,51,63)]
 assert 3*71<2*(2*63)
 print('surviving (M,S,n,W234):',surv)
if __name__=='__main__':main()
