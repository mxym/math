"""Three rank-48 quadratic rows force the eight 44-sets to agree at every C."""
from fractions import Fraction as F
from math import isqrt
from collections import defaultdict
from higher_moments import projections, SHIFTS
from two_type_true_hoffman import orb, move, cumul
def basic(a,t):
 return (t>=11*abs(a) and (t-a)%2==0 and not (a==0 and 0<t<14)
         and not(abs(a)==1 and t<=19) and (abs(a),t)not in
         {(0,14),(0,16),(0,20),(0,24),(2,24),(2,26),(2,28),(2,30),(3,37)})
def verify():
 keys=sorted(set().union(*(projections(sh,n) for sh in (None,*SHIFTS) for n in (1,2))))
 by=defaultdict(list)
 for a,t in keys:
  if not basic(a,t):continue
  for d in range(-isqrt(22*t),1+isqrt(22*t)):
   if (d-4*a)%7 or (9*d-22*a)**2>154*(9*t-11*a*a):continue
   if ((a==0 and t in (18,22) and d!=0) or
       ((a,t)==(1,27) and d not in (-3,4)) or ((a,t)==(1,21) and d!=4) or
       ((a,t)==(0,26) and d not in (-7,0,7))):continue
   o=orb((a,t,d))
   if all(basic(*move(o,j)[:2])for j in range(-6,7)):by[a,t].append((d,o))
 os=sorted(set(o for ds in by.values()for _,o in ds));ix={o:i for i,o in enumerate(os)}
 # Each variable is folded (raw / 8 on a nonisotropic residual norm, raw otherwise).
 # A literal charge-zero shell counts both signs; angle d distinguishes the signed fields.
 sizes={(0,0):1,(0,18):F(59,2),(0,22):F(91,2),(0,28):2854,(1,21):10,
        (1,23):99,(1,25):79,(1,27):F(531,2),(2,22):27,(2,32):269,
        (3,33):33,(3,35):0,(4,44):1}
 co={(0,0):F(662,21),(0,18):F(412,63),(0,22):F(28,9),(0,28):F(55,63),
     (1,21):F(440,27),(1,23):-F(986,567),(1,25):F(232,567),(1,27):F(664,81),
     (2,22):-32,(2,32):-F(134,567),(3,33):-F(124,63),(3,35):F(158,21),(4,44):F(464,63)}
 lhs=[F(0)for _ in os]
 for k,w in co.items():
  for d,o in by[k]:lhs[ix[o]]+=w
 sh=(-1,1,-1,1)
 for h,w in [((0,0,0,0),-F(5,11907)),((1,0,0,0),F(1,13608)),((0,1,0,0),F(5,13608))]:
  u,v=[cumul(sh,n,projections(sh,n),h,1,by,ix,2)for n in (1,2)]
  lhs=[s+w*(j+48*i)for s,i,j in zip(lhs,u,v)]
 rhs=[0]*len(os)
 for k,d,w in [((0,28),7,8),((1,23),-3,-8),((1,23),11,24),((2,22),1,-32),
               ((4,44),16,3),((1,25),11,8),((1,27),-3,4),((3,35),12,3)]:
  fold=1 if (9*k[1]-11*k[0]*k[0])%7==0 else 8
  rhs[ix[dict(by[k])[d]]]+=w*fold
 assert lhs==rhs
 const=sum(co[k]*v for k,v in sizes.items())
 assert const==4072
 from cost21_integer_filtration import model
 model(expected_w=sizes)
 print("Three exact quadratics; raw constant",const,"; after ordinary site marks",const+8*22)
if __name__=='__main__':verify()
