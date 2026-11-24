"""Unaveraged norm-four, rank-48 quadratic on the {018,121,125} face."""
from itertools import product, combinations_with_replacement
from collections import Counter
from fractions import Fraction

B = ((2,1,0,0),(1,4,0,0),(0,0,2,1),(0,0,1,4))
D = ((4,-1,0,0),(-1,2,0,0),(0,0,4,-1),(0,0,-1,2)) # 7 B^{-1}
shifts = (None,(-2,0,0,0),(-2,1,0,0),(-1,1,-1,1))
pairs = list(combinations_with_replacement(range(4),2))
zero = (0,0,(0,0))

def dot(x,y): return sum(u*v for u,v in zip(x,y))
def times(b,x): return tuple(dot(row,x) for row in b)
def anti(x): return min(tuple(x),tuple((-z)%7 for z in x))

def pts(sh):
    den = 1 if sh is None else 3
    if sh is None: cos = [((0,0,0,0),1)]
    else: cos = [(tuple(j*x%3 for x in times(B,sh)),3) for j in (-1,0,1)]
    for offs,step in cos:
        # conservative bounds from (h,e_i)^2 <= 4 B_ii
        m = 4*den
        for g in product(*[range(-m+(m+o)%step,m+1,step) for o in offs]):
            h = dot(g,times(D,g))
            q = 28*den**2-h
            if q < 0: continue
            for a in ((0,3) if sh is None else (((-dot(sh,g)+4)%9-4),)):
                if a < 0: continue
                n,r = divmod(9*q+11*a*a*den**2,9*den**2)
                if r or n<11*a or (n-11*a)%2 or (a==0 and 0<n<14) or (a==1 and n<=19) or (a,n)==(2,24): continue
                # Implied FULL shell vanishings, not a general unit/full identification.
                if (a,n) in ((0,16),(0,20),(0,24),(2,26),(2,28),(2,30),(3,37)): continue
                c=tuple((g[i]+5*g[i+1])*pow(den,-1,7)%7 for i in (0,2))
                yield a,n,g,c,(2 if a else 1)

def row(o,sh,ij,points):
    i,j=ij; res=Counter(); den=1 if sh is None else 3
    def harm(g):return 2*g[i]*g[j]-B[i][j]*g[0]**2
    for a,n,g,c,m in points:
        v=anti(tuple(dot(r,c)%7 for r in o))
        if (a,n)==(1,27): a,n,m=0,18,9*m
        if (a,n)==(0,26): a,n,m=1,21,8*m
        res[a,n,v]+=m*harm(g)
    for k in (0,2):
        if sh is None or dot(B[k],sh)%3==0:
            res[zero]+=2*48*harm([den*x for x in B[k]])
    return res


from itertools import groupby
import sympy as sm
allpts={s:list(pts(s)) for s in shifts}
basis={}
def reduce(x):
 while x:
  i=min(x);v=x[i]
  if i not in basis:
   basis[i]={j:Fraction(w,v)for j,w in x.items()};return
  for j,w in basis[i].items():
   z=x.get(j,0)-v*w
   if z:x[j]=z
   else:x.pop(j,None)
group=[((i,j),((-t*j)%7,(t*i)%7)) for i,j in product(range(7),repeat=2) if (i*i+j*j)%7==1 for t in (1,-1)]
K=set()
for o in group:
 for sh in shifts:
  for ij in pairs:
   rr={k:z for k,z in row(o,sh,ij,allpts[sh]).items() if z and k[-1]!=(0,0)};K.update(rr);reduce(rr)
K=sorted(K)
for at,ls in groupby(K,key=lambda k:k[:2]):reduce(dict.fromkeys(ls,1))
NK=sm.Matrix([[r.get(k,0) for k in K] for r in basis.values()]).nullspace()
H=sm.Matrix.hstack(*NK);f=lambda a,n,i:K.index([k for k in K if k[:2]==(a,n)][i]);U=H[[f(1,21,0),f(1,21,2),f(1,25,0),f(3,33,0)],:];H=H*U.inv()
def test(k,m):
 assert H[[f(*k,i)for i in range(4)],:]==sm.Matrix(m)
test((1,21),[(1,0,0,0),(-1,0,0,0),(0,1,0,0),(0,-1,0,0)])
test((4,44),[(-Fraction(349,62),0,0,0),(Fraction(349,62),0,0,0),(0,-Fraction(349,62),0,0),(0,Fraction(349,62),0,0)])
assert H[[f(0,18,i)for i in range(4)],2:]==sm.Matrix([[Fraction(a,18),0] for a in (-1,1,1,-1)])
assert H[[f(1,25,i)for i in range(4)],2:]==sm.Matrix([[a,0]for a in (1,-1,-1,1)])
assert len(K)==36 and len(basis)==32
print('36 opposite-residue deviations, exact nullity four; G444/U121 and N18/U125 relations verified.')
