#!/usr/bin/env python3
"""A product-sphere/phase code LP certificate for simple quarter turns. Standard Python."""
from fractions import Fraction as F
from math import comb
import sys
ROWS={"2":[[0,3,88083],[1,0,17776699],[1,1,199323],[1,3,198538],[2,0,10745752],[2,2,53812],[2,4,48822],[3,0,3194408],[4,1,1712799],[4,3,41128],[5,1,2398909],[5,3,161586],[6,1,1088503],[6,3,27843],[8,0,16325],[8,2,75484],[8,4,30913]],"3":[[0,1,2055543],[0,3,557197],[0,5,230312],[1,0,26350041],[1,1,2094742],[1,3,1442392],[1,5,190762],[2,0,23763789],[2,2,1922316],[3,0,11274304]],"4":[[0,1,3712772],[0,5,52739],[1,0,32530819],[1,1,5379457],[1,2,1188132],[1,5,109954],[2,0,38650078],[2,2,2462730],[3,0,20079594],[3,2,2330077],[10,1,673655]],"5":[[0,1,4568070],[0,3,587863],[1,0,40299648],[1,1,8701683],[1,5,730123],[2,0,51628609],[2,1,3520894],[2,2,5013813],[2,4,460414],[3,0,28853673],[3,4,6634977]]}
ROWS={int(k):v for k,v in ROWS.items()}
def req(x):
 if not x:raise ValueError('failed certificate')
class P(dict):
 def __init__(self,a=0):super().__init__(a if isinstance(a,dict) else ({(0,0):F(a)} if a else {}))
 def __add__(self,o):
  q=P(self)
  for k,v in P(o).items():q[k]=q.get(k,0)+v
  return P({k:v for k,v in q.items()if v})
 __radd__=__add__
 def __mul__(self,o):
  q=P()
  for (a,b),v in self.items():
   for (c,d),w in P(o).items():k=a+c,b+d;q[k]=q.get(k,0)+v*w
  return P({k:v for k,v in q.items()if v})
 __rmul__=__mul__
 def __neg__(self):return self*(-1)
 def __sub__(self,o):return self+-P(o)
 def __rsub__(self,o):return P(o)+-self
def bern(p):
 L=max(i for i,j in p);D=max(j for i,j in p)
 T=[[sum(p.get((k,j),0)*F(comb(i,k),comb(L,k))for k in range(i+1))for j in range(D+1)]for i in range(L+1)]
 den=1<<40
 return [[(sum(T[i][h]*F(comb(j,h),comb(D,h))for h in range(j+1))*den).__ceil__()for j in range(D+1)]for i in range(L+1)]
def half(row):
 a=list(row);b=[a[0]];c=[a[-1]]
 while len(a)>1:
  a=[(v+w+1)//2 for v,w in zip(a,a[1:])];b.append(a[0]);c.append(a[-1])
 return b,c[::-1]
def check(rows,k=0):
 if max(map(max,rows))<=0:return 1
 if any(rows[i][j]>0 for i in (0,-1)for j in (0,-1)):raise RuntimeError('positive endpoint after outward rounding '+str((k,rows[0][0],rows[-1][-1])))
 if k>55:raise RuntimeError('unresolved square')
 if k%2==0:
  a=list(zip(*rows));b,c=zip(*[half(r)for r in a]);B=list(zip(*b));C=list(zip(*c))
 else:B,C=zip(*[half(r)for r in rows])
 return 1+check(B,k+1)+check(C,k+1)
def main(d):
 rows=ROWS[d];maxN={2:4,3:7,4:11,5:16}[d];eps={2:F(15,1000),3:F(14,10000),4:F(1,100),5:F(2,100)}[d]
 x=P({(1,0):F(1)});y=P({(0,1):F(1)})
 z=F(707106,10**6)+(1-F(707106,10**6))*y;t=-1+(2-z)*x
 pp=[P(1),t];tt=[P(1),z];L=max(r[0]for r in rows);K=max(r[1]for r in rows)
 for l in range(1,L):
  if d==2:pp.append(2*t*pp[l]-pp[l-1])
  else:pp.append(F(2*l+d-2,l+d-2)*t*pp[l]-F(l,l+d-2)*pp[l-1])
 for j in range(1,4*K):tt.append(2*z*tt[j]-tt[j-1])
 pol=P(1-eps)
 for l,k,v in rows:
  req(v>=0 and l+k>0);pol+=F(v,10**7)*pp[l]*tt[4*k]
 n=check(bern(pol));bound=1+sum(F(v,10**7)for l,k,v in rows)/(1-eps);req(bound<maxN+1)
 print('PASS fixed dimension',d,'moving noncentral square orbits <=',maxN,'bound',bound,'boxes',n,flush=True)
if __name__=='__main__':
 for d in map(int,sys.argv[1:] or [2,3,4,5]):main(d)
