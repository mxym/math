"""Replay the original/extension single-site two-cusp chart; all arithmetic is exact."""
import json
import sympy as sm
from fractions import Fraction as F
from math import lcm,gcd
from functools import cache, reduce
from itertools import product
from collections import Counter,defaultdict
from pathlib import Path
import runpy
from higher_moments import rows,projections,SHIFTS,GRAM,dot,times
from rank36_three_types import UNIT
from site_degree_ten import orbit,values,admissible,harmonic
HERE=Path(__file__).resolve().parent
class Vec(list):
 def __add__(self,o):return Vec(a+b for a,b in zip(self,o))
 def __sub__(self,o):return Vec(a-b for a,b in zip(self,o))
 def __mul__(self,t):return Vec(t*v for v in self)
 def __rmul__(self,t):return self*t
 def __iadd__(self,o):return self+o
 def __isub__(self,o):return self-o

chs=[((1,25),(0,16),8),((1,27),(0,18),9),((1,27),(2,26),2),((0,26),(1,21),8)]
def simp(v):
 q=[F(x) for x in v];d=lcm(*(x.denominator for x in q));z=[int(d*x) for x in q];g=reduce(gcd,z,0) or 1
 return [x//g for x in z]
@cache
def hp(d,ip,v2,n):
 f=[F(1)]
 for j in range(d//2):f.append(-f[-1]*F((d-2*j)*(d-2*j-1),2*(j+1)*(n+2*d-2*j-4)))
 L=lcm(*(c.denominator for c in f))
 return sum(int(c*L)*ip**(d-2*j)*v2**j for j,c in enumerate(f))
@cache
def fourier(RR,d):
 form=runpy.run_path(str(HERE.parents[1]/'maximal-marked-lattice'/'verify.py'))['form']
 def conv(a,b):
  return [sum(a[i]*b[j-i] for i in range(j+1))for j in range(28)]
 k=22+d;dim=1+2*(k//3);bs={};ws={}
 for a,l,r in product(range(3,k//2+1,2),(0,1),(0,1)):
  b=k-a;x=list(map(F,conv(form(a,l),form(b,r))));pw=(2*l-1)*((a-1)//2)+(2*r-1)*((b-1)//2);y=[F(7)**pw*u for u in conv(form(a,1-l),form(b,1-r))]
  for i in range(dim):
   c=x[i]
   if not c:continue
   if i not in bs:bs[i]=[z/c for z in x];ws[i]=[z/c for z in y];break
   x=[z-c*t for z,t in zip(x,bs[i])];y=[z-c*t for z,t in zip(y,ws[i])]
 assert len(bs)==dim,(len(bs),dim,d)
 mat=sm.Matrix([bs[i][:22]+[v*7**(RR//2-11+d//2)for v in ws[i][:4]]for i in sorted(bs)])
 return [simp(list(col)) for col in mat.nullspace()]
def calc(RR,cert):
 P=7**((44-RR)//2)+1
 shs=[None,*SHIFTS];raw=rows();tabs={(i,n):projections(h,n)for i,h in enumerate(shs)for n in (1,2,3)}
 keys=sorted(set().union(*raw,*tabs.values()));zset=set();by=defaultdict(list)
 for a,t in keys:
  for k in values(a,t):
   z=orbit((a,t,k))
   if admissible(z):by[a,t].append((k,z));zset.add(z)
 def iso(a,t,k=0):return (9*t-11*a*a)%7==0
 atoms=sorted(zset); cols=[('W',z)for z in atoms]+[('C',z)for z in atoms if iso(*z)]
 ix={k:i for i,k in enumerate(cols)};N=len(ix)
 def zr():return Vec([0]*N)
 def val(kt,f=lambda k:1,sector='W'):
  a,t=kt;z=zr()
  for k,o in by[kt]:
   w=f(k)
   if sector=='W':z[ix['W',o]]+=w
   elif sector=='C':z[ix['C',o]]+=w
   else:
    z[ix['W',o]]+=P*w
    if iso(a,t):z[ix['C',o]]-=(P-1)*w
  return z
 def w(k):return val(k)
 def c(k):return val(k,sector='C')
 def glob(k):return val(k,sector='G')
 def lin(rs):return sum((v*w(k)for k,v in rs.items() if v),zr())
 eq=[];ub={};one=w((0,0))
 def add(a):
  if any(a):eq.append(simp(a))
 for row in raw:
  r=dict(row)
  for target,src,m in chs:r[src]=r.get(src,0)-m*row.get(target,0)
  add(lin(r))
 for a,t in keys:
  for s in (['W','C'] if iso(a,t) else ['W']):
   for f in [lambda k:9*k+a,lambda k:99*k*k-t]:add(val((a,t),f,s))
 for z in atoms:
  if iso(*z):
   row=zr();row[ix['W',z]]=1;row[ix['C',z]]=-1;ub['compat'+str(z)]=row
 add(one-c((0,0)))
 un={k:w(k)-sum((m*w(s)for q,s,m in chs if q==k),zr())for k in UNIT}
 ub.update({('u',k):x for k,x in un.items()})
 def ah(n,d,shn,h):
  nr=1 if shs[shn] is None else 3
  ax=252+9*dot(h,times(GRAM,h));z=zr()
  for (a,t),vs in tabs[shn,n].items():
   cnt=Counter((3//nr)*dot(u,h) for u in vs)
   z+=(1+(a!=0))*val((a,t),lambda k:sum(m*harmonic(d,9*k+a+q,ax*2*n)for q,m in cnt.items()))
  return z
 for dd in (2,4,6,8,10):
  for si,sh in enumerate(shs):
   for h in [(0,0,0,0),(1,2,3,1),(1,-1,1,-2)]:
    f,g,j=[ah(n,dd,si,h)for n in (1,2,3)]
    if dd==2:add(g+48*f);add(j+195804*f)
    else:
     a,b={4:(151740,192),6:(-99180,-552),8:(50220,432),10:(-22140,-312)}[dd];add(j-a*f-b*g)
 def moments(d,j,s):
  z=zr()
  for a,t in ((0,2*j),(3,2*j+11)):
   if (a,t) in by:z+=(1+(a!=0))*val((a,t),lambda k:hp(d,9*k+a,36*2*j,44),s)
  return z
 for dd in (0,4,6,8,10,12,14,16):
  fr=fourier(RR,dd)
  xy=[moments(dd,j,'G')for j in range(22)]+[moments(dd,j*7,'C')for j in range(4)]
  for v in fr:add(sum((h*row for h,row in zip(v,xy)if h),zr()))
 for ky,hist,m in [((1,23),{3:1,-1:14,0:84},99),((2,36),{2:2,-2:1,-1:24,0:72},693),
                   ((0,42),{3:1,-3:1,1:12,-1:12,0:73},8316),((3,39),{1:3,-1:36,0:60},231),
                   ((3,53),{2:2,1:1,-2:3,-1:32,0:61},8316)]:
  for k,h in hist.items():ub['mark'+str((ky,k))]=99*val(ky,lambda i:int(k==i),'C')-m*h*one
 ub['c353']=c((3,53))-16371*one
 ub['six']=99*val((3,53),lambda i:69*(i**4-i*i)+92*(i**3-i),'C')-(8316*3588+8055*552)*one
 ub['coco']=99*val((3,39),lambda i:int(i==2),'C')-22*c((2,22))
 ub['n16']=6930*one-glob((0,16));ub['n18']=289520*one-glob((0,18));ub['N']=990*one-glob((0,14))
 ub['w14']=4*one-w((0,14));ub['y2']=moments(0,14,'C')-462*one;ub['y3']=moments(0,21,'C')-44804*one
 ub['121']=44352*one-glob((1,21));ub['lift']=un[1,27]-w((0,16))
 for i,a in enumerate(cols):
  z=zr();z[i]=1;ub['nonneg'+str(a)]=z
 # Eliminate graph-independent common equations; class counts are still not assumed integral.
 m,piv=sm.Matrix(eq).to_DM().rref();mat=m.to_Matrix()
 free=[j for j in range(N)if j not in piv]
 assert (len(keys),len(atoms),N,len(eq),len(piv))==(60,172,205,295,184)
 def red(v):
  return [F(v[j])-sum(F(v[k])*F(mat[i,j]) for i,k in enumerate(piv) if v[k] and mat[i,j])for j in free]
 for codes,terms in cert:
  allowed={divmod(k,100)for k in codes}
  assert allowed<=UNIT and len(allowed)==(4 if RR==36 else 3)
  positive=dict(ub)
  if not allowed&{(0,16),(0,20)}:positive['n18b']=16166*one-glob((0,18))
  if (0,20)not in allowed:positive['fn']=198*one-glob((0,14))
  if not allowed&{(0,20),(0,24)}:positive['fn2']=112*one-glob((0,14))
  guide={str(k):v for k,v in positive.items()}
  assert len(terms)==len(dict(terms))
  target=one
  for name,coeff in terms:
   coeff=F(coeff);assert coeff>0
   target=target+guide[name]*coeff
  # Verification of one+sum(positive*nonnegative)=0 on the stated face.
  fixed=sm.Matrix([red(un[k]) for k in sorted(UNIT-allowed)])
  r1=fixed.to_DM().rref()[1];r2=fixed.col_join(sm.Matrix([red(target)])).to_DM().rref()[1]
  assert r1==r2
  print("rank",RR,"disallows support contained in",codes,";",len(terms),"positive terms")
if __name__=='__main__':
 data=json.loads((HERE/'original-site-population-duals.json').read_text())
 for rank,rows0 in data.items():calc(int(rank),rows0)
