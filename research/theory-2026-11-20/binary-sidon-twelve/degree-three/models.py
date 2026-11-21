from field import gm as M,iv,p3,check
from itertools import product
from collections import Counter,defaultdict
from pathlib import Path
import json
sq=[M[i][i]for i in range(64)]
rt=[sq.index(i)for i in range(64)]
def tr(x):
 v=0
 for _ in range(6):v^=x;x=sq[x]
 return v
check(tr(32)==1,"trace")
def canonb(x):
 a=[x]
 for i in range(5):a.append(sq[a[-1]])
 return x==min(a)
mod=[(1,0,a,0,b)for a in (0,32)for b in range(1,64)if canonb(b)]
for c in (1,2,4):
 V={sq[sq[t]]^M[c][t]for t in range(64)}; check(len(V)==(16 if c==1 else 64),"SS normal form")
 for b in range(64):
  if b!=min(b^z for z in V):continue
  for f in (0,M[32][sq[c]]):mod.append((0,c,0,b,f))
def models():
 lab=[];jtab=[];cnt=Counter()
 for a,c,d,b,f in mod:
  # a=a1,c=a3,d=a2,b=a4,f=a6
  E=[(x,y)for x,y in product(range(64),repeat=2)if sq[y]^M[M[a][x]^c][y]==p3[x]^M[d][sq[x]]^M[b][x]^f]
  O=None;points=[O]+E
  if len(points)<66:continue
  def neg(P):
   if P is None:return None
   x,y=P;return x,y^M[a][x]^c
  def double(P):
   if P is None or neg(P)==P:return None
   x,y=P;t=M[M[a][y]^sq[x]^b][iv[M[a][x]^c]]
   X=sq[t]^M[a][t]^d
   Y=M[t][x^X]^y^M[a][X]^c
   return X,Y
  def add(P,Q):
   if P is None:return Q
   if Q is None:return P
   if P==Q:return double(P)
   if P==neg(Q):return None
   x,y=P;u,v=Q;t=M[y^v][iv[x^u]];X=sq[t]^M[a][t]^x^u^d;Y=M[t][x^X]^y^M[a][X]^c;return X,Y
  i3={add(P,double(P))for P in points};S=set(points)
  check(i3<=S and all(add(P,Q)in S for P in points for Q in points),"group law")
  done=set()
  for T in points:
   if T in done:continue
   orbit={add(P,T)for P in i3}
   check(not done&orbit and orbit<=S,"3E coset partition");done|=orbit
   if T is None:
    C=[(0,1,0)]+[(x,y,1)for x,y in E]
   else:
    u,v=T;_,w=neg(T);C=[(1,0,0)]
    for x,y in E:
     if (x,y)==T:C.append((0,1,0));continue
     if x==u:val=M[M[a][y]^sq[x]^b][iv[M[a][x]^c]]
     else:val=M[y^w][iv[x^u]]
     C.append((x,val,1))
   check(len(C)==len(set(C))==len(points),"embedding injective")
   jtab.append(dict(coeff=[a,c,d,b,f],T=T,E=len(C),index=len(S)//len(i3)))
   cnt[len(C),len(S)//len(i3)]+=1
   lab.append(C)
  check(done==S,"all T covered")
 print('raw curves',len(mod),'models',len(jtab),'profile',sorted(cnt.items()),flush=True)
 return lab,jtab
