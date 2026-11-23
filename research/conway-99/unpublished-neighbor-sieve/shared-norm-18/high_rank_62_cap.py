"""Exact 13-row, root/norm-four rank-48 quadratic certificate.
Every coefficient is an integer or a Fraction; no external package or solver.
"""
from fractions import Fraction as F
from itertools import product,combinations_with_replacement
from collections import Counter,defaultdict
from math import isqrt

GRAM = ((2, 1, 0, 0), (1, 4, 0, 0), (0, 0, 2, 1), (0, 0, 1, 4))
DUAL7 = ((4, -1, 0, 0), (-1, 2, 0, 0), (0, 0, 4, -1), (0, 0, -1, 2))
SHIFTS = ((-2, 0, 0, 0), (-2, 1, 0, 0), (-1, 1, -1, 1))
PAIRS = list(combinations_with_replacement(range(4), 2))
def dot(x, y):
    return sum(i*j for i, j in zip(x, y))


def times(matrix, x):
    return tuple(dot(row, x) for row in matrix)


def possible(a, t):
    return (t >= 11*a and (t-11*a) % 2 == 0
            and not (a == 0 and 0 < t < 14)
            and not (a == 1 and t <= 19)
            and (a, t) != (2, 24))


def projections(shift, shell):
    """Return all integral projection numerators at fixed squared norm 2*shell."""
    scale = 1 if shift is None else 3
    bounds = [isqrt(scale**2 * 2 * shell * GRAM[i][i]) for i in range(4)]
    offsets = [((0,)*4, 1)] if shift is None else [
        (tuple(j*x for x in times(GRAM, shift)), 3) for j in (-1, 0, 1)]
    table = defaultdict(list)
    for offset, step in offsets:
        entries = [range(-b + (b+r) % step, b+1, step) for b, r in zip(bounds, offset)]
        for w in product(*entries):
            h = dot(w, times(DUAL7, w))
            if h > 14*shell*scale**2:
                continue
            charges = (0, 3) if shift is None else ((-dot(shift,w)+4) % 9 - 4,)
            for a in charges:
                scaled_norm = (9 // scale**2) * h
                t, rem = divmod(126*shell - scaled_norm + 11*a*a, 9)
                if a >= 0 and rem == 0 and possible(a,t):
                    table[a,t].append(w)
    return table



illegal={(0,16),(0,18),(2,28),(2,30),(3,37)}
def possible0(a,t):
 a=abs(a)
 return possible(a,t) and (a,t) not in illegal
def move(z,j):
 a,t,d=z;a+=2*j;t+=22*j*j+2*d*j;d+=22*j
 k=(a+4)//9
 return a-9*k,t-22*a*k+99*k*k,d-22*k
def canonical(z):
 orbit=[move(z,i)for i in range(-6,7)]
 if any(not possible0(a,t)for a,t,d in orbit):return None
 orbit += [(-a,t,-d)for a,t,d in orbit]
 return min(orbit,key=lambda s:(9*s[1]-11*s[0]**2,s[0],s[2]))
def angles(a,t):
 for d in range(-isqrt(22*t),isqrt(22*t)+1):
  if (d-4*a)%7 or (9*d-22*a)**2>154*(9*t-11*a*a):continue
  if a==0 and t in (20,22) and d:continue
  key=canonical((a,t,d))
  if key is not None:yield d,key
def slot(row,w,a,t,d=None):
 for e,k in angles(a,t):
  if d is None or d==e:row[k]+=w
def pair(K,v):return sum(a*b for a,b in zip(K,v))
def krow(index):
 # Blocks of eleven: 10 traceless K quadratics and the four-dimensional trace row.
 sh=(*SHIFTS,None)[index//11]; j=index%11;sc=3 if sh else 1
 row=Counter()
 for ss,mu in ((1,48),(2,1)):
  for (a,t),gs in projections(sh,ss).items():
   if j<10:
    i,k=PAIRS[j];v=sum(2*g[i]*g[k]-GRAM[i][k]*g[0]*g[0]for g in gs)
   else:v=sum(12*dot(g,times(DUAL7,g))-14*ss*sc*sc for g in gs)
   slot(row,mu*(2 if a else 1)*v,a,t)
 return row
def crow(h):
 sh=SHIFTS[2];v2=9702+9*dot(h,times(GRAM,h));row=Counter()
 for ss,mu in ((1,48),(2,1)):
  for (a,t),gs in projections(sh,ss).items():
   for d,k in angles(a,t):
    row[k]+=(2 if a else 1)*mu*sum(48*(9*d-22*a+dot(g,h))**2-2*ss*v2 for g in gs)
 return row
def proof():
 target=Counter()
 for a,t,d,w in [(1,23,-3,62),(3,39,None,-4),(2,22,None,88),(0,14,None,-7),(0,0,None,-1630)]:slot(target,w,a,t,d)
 pos=[(4,44,16,30),(4,44,9,80),(3,33,12,48),(3,33,5,62),(3,35,12,54),
      (3,35,5,40),(2,26,8,200),(2,32,8,12),(2,32,1,24),(1,21,4,78),
      (1,23,11,62),(1,25,11,62),(1,25,4,72),(1,25,-3,82),
      (1,27,11,112),(1,27,4,150),(1,27,-3,188),(0,14,7,98),(0,14,0,49)]
 for a,t,d,w in pos:slot(target,-w,a,t,d)
 coef=[(4,'-233743/285768'),(7,'98473/95256'),(9,'9178/35721'),
       (10,'-703/63504'),(15,'209/504'),(18,'-12541/13608'),
       (20,'2836/5103'),(21,'11/3024'),(26,'4093/2268'),(43,'1/14')]
 rr=[(krow(i),F(f))for i,f in coef]
 rr += [(crow(h),F(f))for h,f in [((0,0,0,0),'1/2592'),((1,0,0,0),'1/1008'),((0,1,0,0),'-25/18144')]]
 sub=Counter();slot(sub,1,1,27);slot(sub,-2,2,26)
 rr.append((sub,-166))
 for r,w in rr:
  for k,v in r.items():target[k]-=w*v
 bad={k:v for k,v in target.items()if v}
 assert not bad,bad
 print("13 exact quadratic rows. M>=62 needs 166 U127 >=1190; verified all 19 angular terms.")
if __name__=='__main__':proof()
