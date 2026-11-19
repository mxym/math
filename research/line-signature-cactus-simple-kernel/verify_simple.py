"""Supplement to the simple suppressed-kernel argument, not an exhaustive graph proof."""
from verify import *
from collections import Counter
def cycle_edges(k,step=1):return sorted(set(tuple(sorted((i,(i+step)%k))) for i in range(k) if i!=(i+step)%k))
def expand(d,edges,L,marks):
 cc=0;nodes=[];inc=[];internal=[]
 for v in range(d):
  deg=sum(v in (i,j) for i,j in edges)
  ids=list(range(cc,cc+deg-2));cc+=deg-2;nodes.append(ids);ports=[]
  for j,a in enumerate(ids):
   old=(j>0)+(j+1<len(ids));ports += [a]*(3-old)
   if j+1<len(ids):internal.append((a,ids[j+1],4))
  req("port count",len(ports)==deg);inc.append(ports)
 p=[(inc[i].pop(),inc[j].pop(),ell) for (i,j),ell in zip(edges,L)]
 return cc,p+internal,[nodes[i][0] for i in marks]
def go():
 rng=Random(331212);qt=0;found=[0]*4
 for n in range(4,15):
  for dx in [{1,n//2}] if n%2==0 and n>=4 else []:
   if n==4:edges=sorted(set(cycle_edges(n)+cycle_edges(n,n//2)))
   else:edges=sorted(set(cycle_edges(n)+cycle_edges(n,n//2)))
   for rep in range(210):
    L=[rng.choice((3,4,5,6)) for _ in edges];marks=[i for i in range(n) if rng.randrange(4)==0]
    sig0=quotient(n,[(i,j,l) for (i,j),l in zip(edges,L)],marks)
    req("cubic upper",4*sig0<=3*n);qt+=1
  if n>4:
   edges=sorted(set(cycle_edges(n)+cycle_edges(n,2)))
   for rep in range(170):
    L=[rng.choice((3,4,5,6)) for _ in edges];marks=[i for i in range(n) if rng.randrange(4)==0]
    sigma=quotient(n,[(i,j,l) for (i,j),l in zip(edges,L)],marks);b,p,h=expand(n,edges,L,marks)
    req("simple lift",len(set(tuple(sorted((i,j))) for i,j,l in p))==len(p) and all(i!=j for i,j,l in p))
    req("cubic degrees",all(sum(v in (i,j) for i,j,l in p)==3 for v in range(b)))
    req("signature",quotient(b,p,h)==sigma);req("strong upper",4*sigma<=3*b);qt+=1
 print("PASS exact simple cubic kernels and lifts of simple four-regular ones:",qt)
if __name__=='__main__':go()
