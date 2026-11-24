"""Run in shared-norm-18 (SymPy), with original_site_populations.py and its dependencies."""
import sympy as sm
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
                if (a,n) in ((0,16),(0,18),(0,20),(0,24),(1,21),(1,25),(1,27),(2,26),(3,37)): continue
                c=tuple((g[i]+5*g[i+1])*pow(den,-1,7)%7 for i in (0,2))
                yield a,n,g,c,(2 if a else 1)

from itertools import product,combinations
from math import comb
def comps(n,k,p=()):
 if k==1:yield (*p,n);return
 for i in range(n+1):yield from comps(n-i,k-1,(*p,i))
def out(k,tot,ps,os):
 E,O,ed,od=maps[k];N=[]
 for e,o in zip(E,O):
  v=sum(a*b for a,b in zip(e,ps));w=sum(a*b for a,b in zip(o,os))
  for s in (1,-1):
   p=ed*od*tot+od*v+4*ed*s*w
   if p%(8*ed*od) or p<0:return None
   N.append(p//(8*ed*od))
 return N
maps={
 230:([(0,-3,-3),(3,0,3),(-3,0,-3),(0,3,3)],[(5,-15,15,-5),(-5,-15,-5,15),(-15,5,15,5),(15,5,5,15)],4,14),
 444:([(3,9,0),(9,3,0),(-9,-9,-6),(-3,-3,6)],[(12,0,3,-3),(0,12,3,3),(-3,-3,-12,0),(3,-3,0,-12)],4,7),
 228:([(1,-17,0),(17,17,18),(-1,-1,-18),(-17,1,0)],[(1,0,-5,5),(5,5,-1,0),(-5,5,0,-1),(0,1,-5,-5)],12,7),
 129:([(-13,5,0),(-5,-5,-18),(13,13,18),(5,-13,0)],[(-5,0,25,-25),(-25,-25,5,0),(25,-25,0,5),(0,-5,25,25)],12,7)}


def verify_maps():
 from itertools import groupby
 ps={s:list(pts(s)) for s in shifts}
 group=[((i,j),((-t*j)%7,(t*i)%7)) for i,j in product(range(7),repeat=2)
        if (i*i+j*j)%7==1 for t in (1,-1)]
 assert len(group)==16
 for mode in ('even','odd'):
  basis={}; K=set()
  def reduce(x):
   while x:
    i=min(x);v=x[i]
    if i not in basis:
     basis[i]={j:Fraction(w,v) for j,w in x.items()};return
    for j,w in basis[i].items():
     z=x.get(j,0)-v*w
     if z:x[j]=z
     else:x.pop(j,None)
  for o in group:
   for sh in shifts:
    for i,j in pairs:
     r=Counter()
     for a,n,g,c,m in ps[sh]:
      if c==(0,0) or (a==0 and mode=='odd'):continue
      b=tuple(dot(ro,c)%7 for ro in o);v=anti(b)
      r[100*a+n,v]+=m*(2*g[i]*g[j]-B[i][j]*g[0]**2)*(1 if mode=='even' or v==b else -1)
     r={k:z for k,z in r.items() if z};K.update(r);reduce(r)
  K=sorted(K)
  if mode=='even':
   for _,ls in groupby(K,key=lambda k:k[0]):reduce(dict.fromkeys(ls,1))
  N=sm.Matrix.hstack(*sm.Matrix([[r.get(k,0) for k in K]for r in basis.values()]).nullspace())
  def shell(k): return N[[i for i,(at,_) in enumerate(K) if at==k],:]
  print(mode, len(K),len(basis),N.cols)
  assert (len(K),len(basis),N.cols)==((36,32,4) if mode=='even' else (28,24,4))
  for k,(E,O,ed,od) in maps.items():
   assert shell(k)==(sm.Matrix(E)*shell(335)[:3,:]/ed if mode=='even' else sm.Matrix(O)*shell(335)/od)
  if mode=='odd': assert shell(335).rank()==shell(444).rank()==4
verify_maps()
from sympy.matrices.normalforms import hermite_normal_form
L=84;D0=8*L
def mat(u,A,D,p):
 C=list(u)+[A-sum(u)];P=[4*(a+b)-A for a,b in zip(C[::2],C[1::2])];Q=[a-b for a,b in zip(C[::2],C[1::2])]
 ret=[]
 for k,tot in [(444,D),(230,4+4*p+A+2*D),(228,A+D),(129,5*A-D)]:
  E,O,ed,od=maps[k]
  for e,o in zip(E,O):
   v=sum(a*b for a,b in zip(e,P));w=sum(a*b for a,b in zip(o,Q))
   for sign in (1,-1):ret.append(L*tot+L//ed*v+4*(L//od)*sign*w)
 return sm.Matrix(ret)
U=[0]*7;x0=mat(U,0,0,0);cols=[]
for i in range(7):
 u=U[:];u[i]=1;cols.append(mat(u,0,0,0)-x0)
C=hermite_normal_form(sm.Matrix.hstack(*cols,D0*sm.eye(len(x0)))).inv()
for p in (0,1):
 res=[]
 for A,D in product(range(8),repeat=2):
  if all(v.q==1 for v in C*mat(U,A,D,p)):res.append((A,D))
 print('parity',p,len(res),res)
 assert res==[(0,0),(2,2),(4,4),(6,6)]
for h in range(0,18,2):
 steps=0;passp=0;stepss=0;hit=0
 for A in range(h+1):
  D=h-A;cs=[(444,D),(230,1732+A+2*D),(228,784+h),(129,7088+5*A-D)]
  for p in comps(A,4):
   ps=[4*v-A for v in p[:3]];steps+=1
   def good(k,n):
    E,O,ed,od=maps[k]
    return all((ed*n+sum(x*y for x,y in zip(v,ps)))%(4*ed)==0 and ed*n+sum(x*y for x,y in zip(v,ps))>=0 for v in E)
   if not all(good(k,n)for k,n in cs):continue
   passp+=1
   for os in product(*(range(-v,v+1,2)for v in p)):
    stepss+=1
    if all(out(k,n,ps,os) is not None for k,n in cs):hit+=1
 print('small',h,steps,passp,stepss,hit)
 assert hit==0

from original_site_populations import calc
from rank36_three_types import UNIT
import sympy as sm
o,w,c,g,u,ub,red=calc(42,[],export=True)
A=sm.Matrix([red(u[k])for k in sorted(UNIT-{(0,26),(2,28),(2,30)})]);H=sm.Matrix.hstack(*A.nullspace())
def qq(k):return g(divmod(k,100))
B=w((0,14));S=w((1,23))-99*o-7*B;M=w((2,22));h=qq(335)+qq(444)
d=qq(444);a=qq(335)
for z in (2*qq(333)-808*o-16*(M+S)-96*B-h,qq(228)-784*o-8*S-56*B-h,
 qq(230)-1732*o-12*(S-M)-96*B-a-2*d, qq(129)-7088*o-32*S-40*M-296*B-5*a+d):
 assert not any(sm.Matrix([red(z)])*H)
print('four physical mass identities verified')
