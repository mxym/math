"""Projective order-two identity and the finite checks for the empty literal small populations.
Standard library only. Run: python g335_projective_trade.py
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import lcm

def anti(v):return min(v,tuple((-x)%7 for x in v))
def axis(v):return 1 if 0 in v else -1
def coefficients():
 c=Counter();aux=Counter()
 for g in product(range(-4,5),repeat=4):
  a,b,h,j=g
  d=4*a*a-2*a*b+2*b*b+4*h*h-2*h*j+2*j*j
  for charge in (0,3):
   t=28+11*(charge==3)-d
   if t<11*charge or (not charge and 0<t<14)or (t-11*charge)%2:continue
   x,y=(a+5*b)%7,(h+5*j)%7
   for z in range(4):
    key=(100*charge+t,anti((x,y)));mult=(-1)**z*(2 if charge else 1)
    c[key]+=mult;aux[key]+=mult*(2*b*b-4*a*a)
    x,y=(2*x+2*y)%7,(-2*x+2*y)%7
 fac={20:1,24:-1,26:-1,335:-2,337:-2}
 assert {(k,v):s for (k,v),s in c.items()if s}=={(k,v):-4*aa*axis(v)for k,aa in fac.items()for k2,v in c if k2==k}
 small={(k,v):s for (k,v),s in aux.items()if s and k not in (20,24,26,337)}
 assert small=={(k,v):-40*axis(v)for k,v in c if k==335}
def configs():
 # Projective masses 3,3,3,3. Signed choices in four directions.
 for i,j,k,l in product(range(4),repeat=4):
  a,b,c,d=[2*z-3 for z in (i,j,k,l)]
  if (a-2*(c+d))%7 or (b-2*(c-d))%7:continue
  yield ([(1,0)]*i+[(-1,0)]*(3-i)+[(0,1)]*j+[(0,-1)]*(3-j),
         [(2,2)]*k+[(-2,-2)]*(3-k)+[(2,-2)]*l+[(-2,2)]*(3-l))
def words(V):
 dic={}
 for m in range(64):
  ids=[i for i in range(6)if (m>>i)&1]
  key=(len(ids),*((sum(V[i][q]for i in ids)%7)for q in (0,1)))
  dic.setdefault(key,[]).append(m)
 return dic
def separating(X,Y):
 xx,yy=words(X),words(Y);rs=[]
 for key,ms in xx.items():
  if not 0<key[0]<=3:continue
  for a in ms:
   if key[0]==3 and a&1:continue
   for b in yy.get(key,[]):rs.append((a,b))
 assert len(rs)==13
 adj=[sum(1<<j for j,(c,d)in enumerate(rs)if i<j and (a&c).bit_count()==(b&d).bit_count())for i,(a,b)in enumerate(rs)]
 def rec(M,J,sigs):
  if len(set(sigs))==12:
   assert len(J)==5
   yield [rs[i]for i in J]
  while M:
   p=M&-M;i=p.bit_length()-1;M-=p;a,b=rs[i];w=a+(b<<6)
   yield from rec(M&adj[i],J+[i],[(s<<1)+(w>>j&1)for j,s in enumerate(sigs)])
 yield from rec((1<<len(rs))-1,[],[0]*12)
def matrix(rs):
 ar=[[F(1)]*12]+[[F((v>>i)&1)for v in (a,b)for i in range(6)]for a,b in rs]
 for j in range(6):
  k=next(k for k in range(j,6)if ar[k][j]);ar[j],ar[k]=ar[k],ar[j]
  d=ar[j][j];ar[j]=[a/d for a in ar[j]]
  for k in range(6):
   if k!=j:
    d=ar[k][j];ar[k]=[a-d*b for a,b in zip(ar[k],ar[j])]
 O=[r[6:]for r in ar];D=lcm(*(v.denominator for R in O for v in R))
 return D,[[int(v*D)for v in R]for R in O]
def candidates(v,w):
 return [d for d in range(-2,29)if (d-4+4*(v[0]*w[0]+v[1]*w[1]))%7==0 and d not in (0,22,23,25)]
def gram(X,Y,rs):
 D,B=matrix(rs);rows=[]
 for i in range(6):
  sets=[candidates(X[i],x)if i!=j else [35]for j,x in enumerate(X)]
  cross=[{D*d for d in candidates(X[i],y)}for y in Y];opts=[]
  for v in product(*sets):
   wy=[sum(v[l]*B[l][j]for l in range(6))for j in range(6)]
   if all(w in ok for w,ok in zip(wy,cross)):opts.append((v,[w//D for w in wy]))
  rows.append(opts)
 order=sorted(range(6),key=lambda i:len(rows[i]));a=[None]*6;nodes=left=0
 def dfs(j):
  nonlocal nodes,left
  nodes+=1
  if j==6:
   for i in range(6):
    for h in range(i+1):
     d=sum(B[l][i]*a[l][1][h]for l in range(6))
     if d not in {D*z for z in ([35]if h==i else candidates(Y[i],Y[h]))}:return
   left+=1;return
  i=order[j]
  for v in rows[i]:
   if all(v[0][h]==a[h][0][i]for h in order[:j]):
    a[i]=v;dfs(j+1)
 dfs(0);return nodes,left
def verify():
 coefficients();count=Counter();total=0
 for X,Y in configs():
  ss=list(separating(X,Y));assert len(ss)==12
  total+=1
  for words0 in ss:count[gram(X,Y,words0)]+=1
 assert total==8 and count=={(62,0):48,(136,0):48}
 print('Tensor/auxiliary rotation coefficients checked; 8 signed patterns, 96 separating maps, no compatible Gram.')
if __name__=='__main__':verify()
