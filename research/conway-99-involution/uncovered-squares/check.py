#!/usr/bin/env python3
if not __debug__:
    raise RuntimeError('Run the certificate checker without -O.')
from itertools import combinations as C, permutations as P,product
from fractions import Fraction as F
from pathlib import Path
import subprocess,tempfile,json,itertools as it
from collections import Counter
def shapes():
 def partitions(k,lo):
  if k==0:yield ();return
  for j in range(lo,k+1):
   for tail in partitions(k-j,j):yield(j,)+tail
 for ends in [((0,1),(12,13)),((0,12),(1,13)),((0,13),(1,12))]:
  same=ends[0][0]//12==ends[0][1]//12
  for d1 in range(2 if same else 1,22,2):
   for d2 in range(d1,23-d1,2):
    if (d1==1 or d2==1)and ends[0][1]==12:continue
    nv=24-(d1+d2+2)
    if nv<0 or nv%2:continue
    for cs in partitions(nv//2,3):
     L=iter(range(2,12));R=iter(range(14,24));E=[];components=[]
     def get(side):return next([L,R][side])
     for (s,t),d in zip(ends,(d1,d2)):
      seq=[s]+[get((s//12+i)%2)for i in range(1,d)]+[t];E.extend(zip(seq,seq[1:]));components.append((False,seq))
     for h in cs:
      seq=[get(i%2)for i in range(2*h)];E.extend(zip(seq,seq[1:]+seq[:1]));components.append((True,seq))
     yield (ends,d1,d2,cs),E,components
masks=['7cf0c','1f996a0','f67e0000','f67e1a00','1757e04a0','1757e44a0','1b5bb2b00','2b6af1a00','4baa65a00','4bcb16300','8ea5c2500','a63475200','c34b53380']
weights=[F(v)for v in ['1/2','421/2340','1/104','7/90','1/13','29/1170','1/13','119/2340','17/1170','61/1170','17/1170','1/39','7/585']]
aut=[4,2,48,1,6,2,2,2,1,1,1,2,2]
def motif(k):
 n=7 if k==0 else 8 if k==1 else 9;g=[set()for j in range(n)];m=int(masks[k],16)
 for i,j in C(range(n),2):
  if m>>(j*(j-1)//2+i)&1:g[i].add(j);g[j].add(i)
 return g
def countaut(g):
 # Edge/nonedge-preserving backtracking within original degree classes.
 p=[];n=len(g)
 def rec():
  i=len(p)
  if i==n:return 1
  s=0
  for v in range(n):
   if v in p or len(g[i])!=len(g[v])or any((j in g[i])!=(u in g[v])for j,u in enumerate(p)):continue
   p.append(v);s+=rec();p.pop()
  return s
 return rec()
def kern():
 K=[0]*13;T={}
 for h in range(13):
  g=motif(h);assert countaut(g)==aut[h]
  if h<2:continue
  for i,j in C(range(9),2):
   if j in g[i]:continue
   A=g[i]-g[j];B=g[j]-g[i];ab=g[i]&g[j];Z=set(range(9))-A-B-ab-{i,j}
   if [len(x)for x in (A,B,ab,Z)]!=[2,2,2,1]:continue
   z=next(iter(Z))
   if not all(any(g[t]&ab for t in S)or S<=g[z]for S in (A,B)):continue
   assert not any(y in g[x]for S in (A,B)for x,y in C(S,2));K[h]+=1
   for L,R in [(A,B),(B,A)]:
    for p,q,t in product(P(L),P(R),P(ab)):
     H=p+q;bits=[a in g[v]for v in H for a in t]+[v in g[u]for u in p for v in q]+[v in g[z]for v in t+H]
     key=sum(1<<j for j,u in enumerate(bits)if u);assert T.get(key,h)==h;T[key]=h
 return T,K
def run():
 here=Path(__file__).resolve().parent;ct=json.loads((here/'cert.json').read_text());den=ct['den'];mult=1000*den;cases=dict(ct['cases']);mark,K=kern();wi=ct['weights'];assert [F(z,den)for z in wi]==[weights[i]*aut[i]/k if k else F(0)for i,k in enumerate(K)]
 print('eligible nonedge marks:',K,'; verified 13 automorphism orders.')
 cnt=Counter();bmin=F(4);amt=0
 with tempfile.TemporaryDirectory()as td:
  p=Path(td);(p/'ker.dat').write_text(''.join('%d %d\n'%a for a in mark.items()));subprocess.run(['c++','-std=c++17','-O2',str(here/'wvec.cpp'),'-o',str(p/'wvec')],check=True)
  for i,(tag,E,_)in enumerate(shapes()):
   ends,d1,d2,_=tag;pr=(d1==1)+(d2==1);s=(d1==2)+(d2==2)if ends[0][1]==1 else 0;cnt[pr]+=1
   if pr:assert i not in cases;continue
   sa=cases.pop(i)
   if s:assert not sa and s>=F(68,195);continue
   assert sa;N=[set()for _ in range(28)]
   def edge(u,v):N[u].add(v);N[v].add(u)
   for u,v in E:edge(u,v)
   for u in range(12):edge(u,26);edge(u+12,27)
   for t in range(2):
    for j in (26,27,t,t+12):edge(t+24,j)
   def rem(u,v):return 2-int(v in N[u])-len(N[u]&N[v])
   rhs={};alpha=dict(sa)
   for u in range(26):rhs[(u,)]=14-len(N[u])-int(u<24 and u%12>=2)
   for u,v in C(range(26),2):rhs[(u,v)]=rem(u,v)
   for u in (*range(2,12),*range(14,24)):rhs[(30,u)]=1
   rhs[()]=71;assert len(rhs)==372;pi={k:alpha.get(j,0)for j,k in enumerate(rhs)};lb=sum(v*pi[k]for k,v in rhs.items())
   def subtract_deficit(cost,e):return min(0,mult*cost-sum(pi[k]for k in e))
   opt=[]
   for off in (0,12):
    qs=[N[off+h]&set(range(12-off,24-off))for h in (0,1)];assert all(len(x)==1 for x in qs);pair=tuple(sorted(next(iter(a))for a in qs));opt.append(pair)
   for off in [0,12]:
    for u,v in C(range(off+2,off+12),2):
     if rem(u,v)==0:continue
     col=[(30,u),(30,v),(u,v)]
     for a,b in ((u,v),(v,u)):
      for h in N[b]:
       if h<26 and h!=a:col.append(tuple(sorted((a,h))))
     w=F(421,1170)*opt.count((u,v));lb+=int(subtract_deficit(w,col))
   Hs=[];words=[]
   for t in ((),(24,),(25,)):
    for A in C(range(12),2-len(t)):
     for B in C(range(12,24),2-len(t)):
      H=A+B+t
      if any(rem(u,v)<=0 for u,v in C(H,2)):continue
      Hset=set(H)
      if any(len(Hset&N[u])+int(u in Hset)>2 for u in range(28)):continue
      Hs.append(H);words.append(sum(1<<v for v in H))
   z=[len(Hs)]+[x for u,v in E for x in (min(u,v),max(u,v)-12)]+words
   raw=subprocess.run([str(p/'wvec')],cwd=p,input=' '.join(map(str,z))+'\n',text=True,capture_output=True,check=True).stdout.splitlines();assert len(raw)==len(Hs)
   for H,row in zip(Hs,raw):
    d=list(map(int,row.split()));assert len(d)==13;w=sum(v*k for v,k in zip(d,wi));col=[()]+[(u,)for u in H]+list(C(H,2));lb+=min(0,1000*w-sum(pi[k]for k in col))
   lb=F(lb,mult);assert lb>=F(68,195),(i,lb);bmin=min(bmin,lb);amt+=1
 print('classes (0/1/2 directions):',*[cnt[i]for i in range(3)],'; exact dual cases:',amt,'minimum:',bmin)
 assert (len(cases),list(map(cnt.get,range(3))),amt)==(0,[74,15,5],59)
 print('Endpoint maximum uncovered squares:',F(144,13)//(2*bmin))
if __name__=='__main__':run()
