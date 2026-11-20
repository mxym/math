"""A check of the known Gold extension attaining six-variable linearity 32."""
from collections import Counter
from itertools import combinations
def mul(a,b):
 z=0
 while b:
  if b&1:z^=a
  b//=2;a*=2
  if a&32:a^=0b100101 # t^5+t^2+1
 return z
def power(a,k):
 z=1
 for i in range(k):z=mul(z,a)
 return z
def truth():
 def tr(x):return x^power(x,2)^power(x,4)^power(x,8)^power(x,16)
 F=[]
 for s in range(64):
  x=s%32;y=s//32;t=tr(x);assert t in (0,1)
  F.append(power(x,3)^(y*(power(x,16)^x))^(32*y*t))
 return F
def check():
 F=truth()
 for h in range(1,64):
  c=Counter(F[x]^F[x^h]for x in range(64));assert len(c)==32 and set(c.values())=={2}
 G=[x+64*F[x]for x in range(64)];assert len({x^y for x,y in combinations(G,2)})==2016
 W=[sum(1-2*(((a&x).bit_count()+(b&F[x]).bit_count())%2)for x in range(64))for a in range(64)for b in range(1,64)]
 assert max(map(abs,W))==32
 # All 64 by 63 component correlations computed; an actual affine component distance is also verified.
 assert min((64-abs(v))//2 for v in W)==16
 return F
if __name__=='__main__':print('APN table:',*check())
