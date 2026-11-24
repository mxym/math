"""Exact low-mass integer filtration on the rank-42 (018,121,125) face."""
from original_site_populations import calc
from rank36_three_types import UNIT
from math import gcd, lcm, ceil
from functools import reduce
from fractions import Fraction as F
import sympy as sm

def model():
 o,w,c,g,u,ub,red=calc(42,[],export=True)
 absent=[red(u[k]) for k in sorted(UNIT-{(0,18),(1,21),(1,25)})]
 # At rank 42 there is just H=0 at seven: the separate eligible-zero and original sectors coincide.
 absent += [red(v) for k,v in ub.items() if str(k).startswith('compat')]
 nul=sm.Matrix.hstack(*sm.Matrix(absent).nullspace())
 row=lambda z:sm.Matrix([red(z)])*nul
 r=w((1,21)); f=F(1,2)*w((0,14)); m=w((2,22)); s=w((1,23))-99*o-14*f; q=g((4,44))
 # For these two positive-charge shells the coefficients at a positive site map
 # to the canonical site's negative-sign key. Dividing by orbit size in W is undone.
 def avg(k):return ub['nonneg'+str(('W',k))]
 x=8*99*avg((-4,44,-1)); y=99*avg((-4,46,-1))
 basis=sm.Matrix.vstack(*(row(v)for v in [o,r,f,m,s,q,x,y]))
 assert basis.shape==(8,8) and basis.det()!=0
 inv=basis.inv()
 test=lambda z:tuple(row(z)*inv)
 assert test(F(1,4)*g((0,18)))==(88,-F(23,6),F(26,3),F(1,3),F(1,2),F(1,24),0,0)
 assert test(w((4,46)))==(720,-18,50,-16,2,F(3,2),0,0)
 extras=[s,w((3,35)),w((4,44)),w((4,46)),g((0,18))-181*o,
         260*o-g((0,18)),114*o-6*m+2*w((4,46))+2*f,r-9*o,13*o-r]
 def prim(rr):
  de=lcm(*(v.q for v in rr));a=[int(z*de)for z in rr]
  g=reduce(gcd,a,0)or 1
  return tuple(z//g for z in a)
 rows=sorted({prim(test(v)) for v in list(ub.values())+extras})
 def apply(z,vs):return sum(i*j for i,j in zip(test(z),vs))
 return rows,test(g((1,25)))

def find():
 rows,u125=model()
 di=lambda n:ceil(F(24*(n-1),n+24))
 counts=[]; corrected=[]
 for r in range(9,14):
  live=[];kept=[]
  for f in range(4):
   for n in range(46,66):
    for m in range(82):
     for s in range(56):
      q=24*(n-88)+92*r-208*f-8*m-12*s
      if not 0<=q<=600:continue
      # x=0 by ||b||^2=44 = -sum b for the (4,44) field.
      t=(1,r,f,m,s,q,0,0)
      lo=0;hi=720-18*r+50*f-16*m+2*s+3*q//2
      if hi<lo:continue
      for a in rows:
       z=sum(i*j for i,j in zip(a[:6],t))
       if a[7]>0:lo=max(lo,-(z//a[7]))
       elif a[7]<0:hi=min(hi,z//(-a[7]))
       elif z<0:break
       if lo>hi:break
      else:
       live.append((f,n,m,s,q,lo,hi))
       # Refine by the exact per-class size/Gram trace from the prior paper.
       amt=sum(i*j for i,j in zip(u125,t))
       assert u125[6]==u125[7]==0
       opts=[]
       for b in range(18,n//2+1):
        a=n-b
        if 72*(a-b)>amt:continue
        cdim=44-di(a)-di(b)-2
        # Only double-subtype (4,46) fields count one-overlap images.
        total446=720-18*r+50*f-16*m+2*s+3*q//2
        # All 41 native cases are Fano-free. Hence A is the ordinary one-overlap graph.
        assert f==0
        ell=m-cdim
        assert cdim>1 and ell>0 and q%4==0
        for edges in range(total446-lo+1):
         # If its spectral radius <=2, eigenvalue 2 occurs in a component on >=3 sites.
         small=ell<=m//3 and ell<=edges//3 and 4*m*ell<=2*edges*cdim
         # With radius >2, at least ell eigenvalues equal 2 in addition to the Perron one.
         big=ell+1<=edges//3 and (4*edges**2*cdim+8*edges*ell*m+4*ell*(m-1)*m**2
                                     <=2*edges*(cdim-1)*m**2)
         if small or big:opts.append((a,b,lo,min(hi,total446-edges),edges));break
       if opts:kept.append((f,n,m,s,q,opts))
  counts.append(len(live));corrected.append(len(kept))
  print(r,'marginals',len(live),'refined',len(kept),'refined Fano counts',sorted(set(v[0]for v in kept)))
  if r in (10,13):print('unrefined:',live,'refined:',kept)
  assert all(v[0]==0 for v in live)
 assert counts==[0,5,12,19,5]
 assert corrected==[0,5,8,4,0]
 return counts,corrected
if __name__=='__main__':print(find())
