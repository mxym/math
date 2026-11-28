#!/usr/bin/env python3
"""Exact, standard-library replay of the eleven-point symmetry-breaking theorem."""
from fractions import Fraction as Q
from itertools import combinations
from functools import lru_cache
def req(b,msg):
 if not b:raise ValueError(msg)
class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.a,self.b=a.a,a.b
  else:self.a=Q(a);self.b=self.a if b is None else Q(b)
 def __add__(x,y):
  y=I(y);return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-I(y)
 def __rsub__(x,y):return I(y)+-x
 def __mul__(x,y):
  y=I(y);v=[a*b for a in (x.a,x.b)for b in (y.a,y.b)];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=I(y);req(y.a*y.b>0,'division across zero');return x*I(1/y.b,1/y.a)
 def mag(x):return max(abs(x.a),abs(x.b))
def f(x):return (x*x)*(x*x-Q(1,4))
def poly(t):return t**5+t**4-4*t**3-3*t**2+3*t+1
br=[(-20,-18),(-14,-12),(-4,-2),(8,9),(16,17)]
for l,h in br:req(poly(Q(l,10))*poly(Q(h,10))<0,'root ordering')
l,h=Q(16,10),Q(17,10)
for _ in range(78):
 m=(l+h)/2
 if poly(l)*poly(m)<=0:h=m
 else:l=m
t=I(l,h);u=[I(2),t]
for j in range(2,6):u.append(t*u[-1]-u[-2])
def cs(r):r%=11;return u[min(r,11-r)]/2
V=[[cs(j*k)for k in range(6)]for j in range(1,6)]
a=(I(Q(1,2))-V[1][4])/(V[1][5]-V[1][4]);x=[r[4]+a*(r[5]-r[4])for r in V]
req(0<a.a<a.b<1 and x[1].a<=Q(1,2)<=x[1].b,'realization')
req(Q(-854,1000)<x[0].a<x[0].b<Q(-853,1000)and all(y.mag()<Q(14,100)for y in x[2:]),'winning lags')
energy=(Q(3,4)+2*sum(f(y)for y in x))/11
req(Q(85379942850,10**11)<-x[0].b<-x[0].a<Q(85379942851,10**11),'mean strength')
req(Q(13060126556,10**11)<energy.a<energy.b<Q(13060126557,10**11),'sharp value')
for k in range(5):
 B=[]
 for j in range(5):
  z=(V[j][5]-V[j][4])/(V[1][5]-V[1][4])
  B.append(V[j][k]-V[j][4]-z*(V[1][k]-V[1][4])if k<4 else -z)
 req(B[0].a>0 and sum(y.mag()for y in B[2:])<24*B[0].a,'lag sensitivity')
req((Q(3,4)+2*f(Q(-85,100)))/11<energy.a and Q(14,100)+24*Q(4,1000)<Q(24,100),'outer and local intervals')
req(4*Q(-85,100)**3-Q(-85,100)/2 < -2 and Q(1,216)<Q(7,100)**2 and Q(7,100)*24<2,'derivative gap')
valid=[]
for m in range(1,32):
 S={j for j in range(1,11)if m>>(min(j,11-j)-1)&1}
 if all((a+b)%11 not in S for a in S for b in S):valid.append(frozenset(S))
can=[{1,10},{1,3,8,10}]
req(set(valid)=={frozenset(i*x%11 for x in s)for i in range(1,11)for s in can},'sum-free strong lags')
for k in range(6):
 y,z,b=V[0][k],V[2][k],V[1][k]
 req((y+Q(4,5)*b+Q(58,100)*z).a>Q(-68,100),'first lower support')
 req((z+Q(22,100)*y).a>Q(-88,100),'second lower support')
 req((y+z+Q(715,1000)*b).a>Q(-1016,1000),'sum lower support')
req(Q(-68,100)-Q(4,5)/2+Q(58,100)/2>Q(-4,5)and Q(-88,100)+Q(22,100)/2>Q(-4,5)and Q(-1016,1000)-Q(715,1000)/2>Q(-138,100),'two-lag consequences')
req((Q(3,4)+2*Q(4,5)**2*Q(13,10)*Q(38,100))/11<energy.a,'two-lag exclusion')
print('PASS sharp transitive value in (0.13060126556,0.13060126557); rank four and strict uniqueness')
# The only possible unordered Fourier pairs at a fixed sum are separated by
# the diagonal and the lag-two diagonal (distinct pair sums of roots).
K=(4,5,6,7);pairs=[(i,j)for i in K for j in K if i<=j]
for r in range(11):req(sum((i+j)%11==r for i,j in pairs)<=2,'Fourier multiplicity')
A=[[1754201,-1340746,-3267,856,4707873,-8541727],[-4594,2590313,-1427,738,-27253,9658650],[-170068,-1435433,-2212226,4483791,-6495711,5542384],[-808418,1498407,1959530,-6641738,6475189,-2687142],[803810,1506008,1956276,6639662,-6460550,-2726719],[172909,-1434543,-2216237,-4482276,6463605,5579560],[-168717,-1430856,2212880,-4484063,-6496251,5542495],[-811050,1498406,-1959579,6643062,6474213,-2685389],[801572,1504160,-1960340,-6638149,-6461295,-2727399],[174499,-1434275,2217795,4481169,6463942,5579459],[-1750521,-1363606,4153,-40,-4658009,-8566166]]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def solve(M,v,pos=True):
 M=[list(map(Q,r))+[Q(v[i])]for i,r in enumerate(M)];n=len(M)
 for k in range(n):
  d=M[k][k];req(d>0 if pos else d!=0,'nonpositive pivot')
  for i in range(k+1,n):
   a=M[i][k]/d
   for j in range(k,n+1):M[i][j]-=a*M[k][j]
 y=[0]*n
 for i in reversed(range(n)):y[i]=(M[i][n]-sum(M[i][j]*y[j]for j in range(i+1,n)))/M[i][i]
 return y
def rank(M):
 B=[list(map(Q,r))for r in M];p=0
 for j in range(len(B[0])):
  i=next((i for i in range(p,len(B))if B[i][j]),None)
  if i is None:continue
  B[p],B[i]=B[i],B[p]
  for i in range(p+1,len(B)):
   u=B[i][j]/B[p][j];B[i]=[a-u*b for a,b in zip(B[i],B[p])]
  p+=1
 return p
req(rank(A)==6,'rank of the asymmetric example')
D=[dot(x,x)for x in A];F=[];adj=[0]*11
for i in range(11):
 r=[]
 for j in range(11):
  h=dot(A[i],A[j]);t=Q(h*h,D[i]*D[j]);r.append(t*(t-Q(1,4)))
  if i!=j:
   req(h<0 or 4*t<1,'not a strict kissing code')
   if h<0 and 4*t>1:adj[i]|=1<<j
 F.append(r)
edges=set()
for v in ((0,1,10),(0,2,3,4,5,10),(0,6,7,8,9,10)):
 edges.update(tuple(sorted((i,j)))for i,j in zip(v,v[1:]))
req({(i,j)for i,j in combinations(range(11),2)if adj[i]>>j&1}==edges,'theta(2,5,5) graph')
@lru_cache(None)
def perfect(m):
 if m==0:return True
 a=m&-m;i=a.bit_length()-1;v=adj[i]&m
 while v:
  b=v&-v
  if perfect(m^a^b):return True
  v^=b
 return False
req(all(perfect(2047^(1<<i))for i in range(11)),'not factor-critical')
z=solve(F,[1]*11);req(min(z)>0,'noninterior minimizing weights');val=1/sum(z)
req(Q(13091705,10**8)<val<Q(13091707,10**8)and val>energy.b,'not a strict separation')
print('PASS connected factor-critical rank-six example in (0.13091705,0.13091707)')
