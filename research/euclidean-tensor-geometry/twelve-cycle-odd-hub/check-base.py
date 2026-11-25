from itertools import product,permutations
from math import gcd
P=1009
z=pow(11,(P-1)//6,P)
assert pow(z,3,P)==P-1 and pow(z,2,P)!=1
C={-5:437,-4:79,-3:503,-2:113,-1:829,1:771,2:821,3:47,4:175,5:67}
def parts(n,a=None):
 if n==0:
  yield ()
  return
 if a is None:a=(n,n)
 for i in range(1,n+1):
  for j in range(min(i,n-i)+1):
   if (i,j)<=a:
    for t in parts(n-i-j,(i,j)):yield ((i,j),)+t
def M(a,b):
 W=[x for i in range(6) for x in (a[i],-b[i])]
 start=W.index(0);W=W[start:]+W[:start];j=0;z=1
 while j<12:
  x=W[j]
  if x==0:j+=1
  elif j+1<12 and W[j+1]==-x:
   z=z*C[-x]%P;j+=2
  else:return 0
 return z
def rank(m):
 r=0
 for j in range(len(m)):
  t=next((i for i in range(r,len(m)) if m[i][j]),None)
  if t is None:continue
  m[r],m[t]=m[t],m[r]; u=pow(m[r][j],-1,P);v=m[r];
  for i in range(r+1,len(m)):
   x=(-m[i][j]*u)%P
   if x:m[i]=[(a+x*b)%P for a,b in zip(m[i],v)]
  r+=1
 return r
count=0
for n in range(6):
 for spec in parts(n):
  count+=1
  L=[0]*(6-n)
  for i,(a,b) in enumerate(spec,1):L+=[i]*a+[-i]*b
  W=sorted(set(permutations(L))); ws=set(W); O=[]
  for v in W:
   if v not in ws:continue
   orbit=[]
   for r in range(6):
    w=v[r:]+v[:r]
    if w in ws:ws.remove(w);orbit.append(w)
   O.append(orbit)
  vals={(v[0],w):M(v[0],w) for v in O for w in W}
  errs=[]
  for g in range(6):
   zz=pow(z,g,P);O2=[o for o in O if pow(zz,len(o),P)==1]
   for o in O2:assert pow(zz,len(o),P)==1
   H=[[sum(pow(zz,k,P)*vals[a[0],w] for k,w in enumerate(b))%P for b in O2] for a in O2]
   errs.append(len(O2)-rank(H))
  expect={((1,1),):[0,1,1,1,1,1], ((2,2),):[4,2,4,4,4,2], ((1,1),(1,1)):[12,6,12,12,12,6]}.get(spec,[0]*6)
  if errs!=expect:raise ValueError((n,spec,errs,expect))
  print(n,spec,len(W),sum(errs),errs,flush=True)
print("profile count",count)
