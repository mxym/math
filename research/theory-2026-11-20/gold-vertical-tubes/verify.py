"""Integer controls. Infinite assertions in README require no computation."""
from itertools import combinations
from math import gcd,isqrt
def require(ok,reason):
 if not ok:raise ValueError(reason)
def field(m,poly):
 q=1<<m
 def mul(x,y):
  z=0
  while y:
   if y&1:z^=x
   y//=2;x<<=1
   if x&q:x^=poly
  return z
 def power(x,n):
  z=1
  while n:
   if n&1:z=mul(z,x)
   n//=2;x=mul(x,x)
  return z
 def tr(x):
  s=0
  for _ in range(m):s^=x;x=mul(x,x)
  require(s in (0,1),'absolute trace');return s
 require(all(power(x,q-1)==1 for x in range(1,q)),'field')
 return mul,power,tr
for m,poly in [(4,19),(6,67)]:
 q=2**m;mul,pw,tr=field(m,poly);E=set(range(q));du=lambda a,b:tr(mul(a,b));N={i for i in E if not tr(i)}
 for k in range(1,m):
  if gcd(k,m)!=1:continue
  e=2**k+1;F=[pw(x,e)for x in range(q)];require(len({((x^y),(F[x]^F[y]))for x,y in combinations(E,2)})==q*(q-1)//2,'Gold graph Sidon')
  for a in E-{0}:
   val={F[x]^F[x^a]for x in E};A=F[a]
   require(val=={mul(A,1^n)for n in N}and len(val)==q//2,'affine derivative')
  for w in E-{0}:
   Q=[du(w,y)for y in F];rad=[h for h in E if all(not(Q[x]^Q[h]^Q[x^h])for x in E)]
   S=sum(1-2*t for t in Q);require(len(rad)<=4 and S*S==q*sum(1-2*Q[h]for h in rad),'squared-sum radical')
  print('Derivative/character checks m,k:',m,k)
 if m!=4:continue
 W=frozenset([0,1,8,9]);E18=[0,1,2,99,68,181,6,40,249,234,219,140,61,14,207,16,129,150]
 require(len(set(E18))==18 and all((pw(z%16,3)^(z//16))in W for z in E18),'18-point tube')
 require(len({x^y for x,y in combinations(E18,2)})==153,'153 pair differences')
 spaces={frozenset([0,x,y,x^y])for x,y in combinations(E-{0},2)}
 cube={pw(x,3)for x in E-{0}};require(len(spaces)==35 and len(cube)==5,'finite catalog')
 exc={w for w in spaces if all(any(du(c,x)for x in w)for c in cube)};orbit={frozenset(mul(c,pw(x,2**j))for x in W)for c in cube for j in range(4)}
 require(exc==orbit and len(exc)==10,'35-space classification')
 for w in exc:
  quotient=lambda x:min(x^y for y in w);F=[pw(x,3)for x in range(16)]
  for a in range(1,16):
   vals=[quotient(F[x]^F[x^a])for x in E if x<x^a]
   require(len(set(vals))==4 and all(vals.count(v)==2 for v in set(vals)),'pair multiplicities in quotient')
 print('m=4 rank-two maxima: 25 at 16, 10 at 18; explicit 18/153 passed.')
print('PASS')
