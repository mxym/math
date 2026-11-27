#!/usr/bin/env python3
"""Exact algebraic necessary tests on absolute eight-dimensional Walsh histograms. Units of four."""
import sys,itertools
from collections import Counter
QWEIGHT={0,64,96,112,120,128,136,144,160,192,256}
# input labels (heights in units of four); a tuple of counts length 11
def yieldspec(pf):
 # all values congruent to zero or four mod eight; any two heights sum <=20
 # norm sum(y^2)=4096. DFS only over all heights >=2 (even) or >=3(odd).
 base=pf
 def dfs(maxv,rem,energy,h):
  if energy<rem*base**2 or energy>rem*maxv**2:return
  if maxv==base:
   if energy==rem*base**2:yield {base:rem,**h}
   return
  if maxv==base+2:
   d,k=divmod(energy-rem*base**2,maxv**2-base**2)
   if k==0 and 0<=d<=rem:
    yield {base:rem-d,maxv:d,**h}
   return
  for x in range(min(rem,(energy-rem*base**2)//(maxv**2-base**2)) + 1):
   if x and (maxv+max(h.keys(),default=0)>20 or x>1 and maxv*2>20):break
   if x:h[maxv]=x
   yield from dfs(maxv-2,rem-x,energy-maxv*maxv*x,h)
   if x:del h[maxv]
 yield from dfs(20-pf,256,4096,{})
def corr(h):
 c=[0]*11
 for x in h:
  for y in h:
   if y>x:continue
   z=h[x]*h[y] if y<x else h[x]*(h[x]-1)//2
   if not z:continue
   if max((x+y)//2,abs(x-y)//2)>10:return None
   c[(x+y)//2]+=z; c[abs(x-y)//2]+=z
 return c
def globaltest(pf,h):
 h={k:v for k,v in h.items() if v}
 if pf:
  # Normalize the spectrum by translation/complement so W/4 is 1 mod4, signed.
  ss={k:(k if k%4==1 else -k) for k in h}
  if abs(sum(h[k]*v for k,v in ss.items()))!=64:return
  qwt=sum(h[k] for k,v in ss.items() if ((v-1)//4)%2)
  if qwt not in QWEIGHT:return
  z=255
 else:
  m=sum(n for k,n in h.items() if k%4==2) # nonmultiples of 16
  if m not in (0,128,256):return
  if m==0:
   if sum(n for k,n in h.items() if k%8==4) not in QWEIGHT:return
  # If residue is constant nonzero 8 mod16 (m=256), W/8 odd; to apply quadratic
  # (W-r)/16 mod2 need signs; no extra test here.
  z=256 if m==128 else 0
 c=corr(h)
 if not c:return
 if any(c[k] for k in [9]):return # |w|=36 never
 if sum(c[1::2])!=128*z or sum(v*(i*i) for i,v in enumerate(c) if i%2)!=1024*z:return
 # O hist four shapes; all combinations in a two-dimensional 2x2 rectangle
 if not 0<=c[7]<=z:return
 t,d=divmod(c[5]+c[7]-18*z,4)
 if d or not 0<=t<=z:return
 if (c[1],c[3])!=(52*z+8*t+3*c[7],58*z-12*t-3*c[7]):return
 # E rows: generic have exactly 64 odd heights (in units of eight), near/bitype 0.
 nE=510-z
 ng,r=divmod(c[2]+c[6]+c[10],64)
 if r or not 0<=ng<=nE:return
 # One generic family for every modulus: exceptional 32 (per non-near),40
 if c[8]+c[10]>nE or c[10]>ng:return
 if c[6]>11*ng:return
 return z,ng,c
if __name__=='__main__':
 for pf in (0,1):
  it=yieldspec(pf);n=0;stats=Counter()
  for h in it:
   n+=1;g=globaltest(pf,h)
   if g is None:continue
   z,ng,c=g;stats[z]+=1
   print(pf, z, ng, *[h.get(i,0) for i in range(21)], ';',*c)
  print('pf',pf,'generated',n,'passed',stats,file=sys.stderr)
