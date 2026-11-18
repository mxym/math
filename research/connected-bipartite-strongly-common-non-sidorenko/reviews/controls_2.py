"""Finite, independent controls for the connected-padding proof; not a proof of the graphon claims."""
from fractions import Fraction as F
from itertools import product
from math import comb
from hashlib import sha256
from pathlib import Path
def ch(s,x):
 if not x:raise ArithmeticError(s)
def av(w,a):return sum(x*y for x,y in zip(w,a))
def mm(W,w,x):return [av(w,[v*z for v,z in zip(row,x)]) for row in W]
def root(W,w):
 K=tuple(tuple(av(w,[a*b for a,b in zip(row,other)]) for other in W) for row in W)
 return tuple(av(w,[v*v for v in row]) for row in K),K
def avgxy(W,xw,yw):
 m=len(xw);n=len(yw)
 X=[sum(xw[i]*yw[j]*yw[l]*W[u][j]*W[i][j]*W[i][l]*W[u][l] for i,j,l in product(range(m),range(n),range(n))) for u in range(m)]
 Y=[sum(yw[i]*xw[j]*xw[l]*W[j][u]*W[j][i]*W[l][i]*W[l][u] for i,j,l in product(range(n),range(m),range(m))) for u in range(n)]
 return X,Y
def go():
 w=[F(1,6),F(1,3),F(1,2)];pairs=[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
 for mask in range(64):
  W=[[0]*3 for _ in w]
  for n,(i,j) in enumerate(pairs):W[i][j]=W[j][i]=F((mask>>n)&1)
  d=[av(w,row) for row in W];p=av(w,d);c,K=root(W,w)
  z=[v-p for v in d];s=av(w,[v*v for v in z]);Lz=mm(W,w,z)
  B=av(w,[a*(b-p**4) for a,b in zip(d,c)])
  r=[av(w,[(v-p*p)**2 for v in row]) for row in K]
  ch('weighted-square identity',B==4*p**3*s+2*p**2*av(w,[a*b for a,b in zip(z,Lz)])+av(w,[a*b for a,b in zip(d,r)]))
  # Compute entire rooted K_{23,13} by grouping the 13 ordered opposite-side draws by type counts.
  for x,deg in enumerate(d):
   val=0
   for i in range(14):
    for j in range(14-i):
     k=13-i-j
     m=comb(13,i)*comb(13-i,j)*w[0]**i*w[1]**j*w[2]**k
     weights=[W[u][0]**i*W[u][1]**j*W[u][2]**k for u in range(3)]
     val+=m*weights[x]*av(w,weights)**22
   ch('full K_{23,13} >= c^143',val>=c[x]**143)
 # Rectangular X,Y of unequal cardinality and weights. W=1+u_i v_j with both centered.
 xw=[F(1,4),F(3,4)];yw=[F(1,2),F(1,3),F(1,6)]
 u=[F(3,4),F(-1,4)];v=[F(1,2),F(-1,2),F(-1,2)]
 W=[[1+a*b for b in v] for a in u]
 # Force both root-type sets to be nontrivial (two signs of different absolute values on Y).
 v=[F(1,2),F(-1,4),F(-1)];W=[[1+a*b for b in v] for a in u]
 ids=list(product(range(2),range(3)));ww=[xw[i]*yw[j] for i,j in ids]
 V=[[W[i][l]*W[k][j] for k,l in ids] for i,j in ids];squared,_=root(V,ww)
 X,Y=avgxy(W,xw,yw)
 ch('crossed kernel exactly Markov',all(av(ww,R)==1 for R in V))
 ch('pointwise product in crossed kernel',all(c==X[i]*Y[j] for c,(i,j) in zip(squared,ids)))
 print('64 nonuniform three-atom graphons: exact weighted positivity identity and all 192 full rooted-biclique bounds.')
 print('One unequal, nonuniform rectangular 2-by-3 Markov kernel: all six exact rooted crossed-product identities.')
if __name__=='__main__':go()
