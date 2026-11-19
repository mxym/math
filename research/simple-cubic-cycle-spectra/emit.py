"""Materialize graph witnesses. Output is consumed by an independent C++ checker."""
import json
from planar import rotation
def need(x):
 if not x:raise ValueError("invalid stream")
def output(fp,n,k,edges,typ,cert):
 print(n,k,len(edges),*(v for e in edges for v in e),typ,len(cert),*(v for e in cert for v in e),file=fp)
G=json.load(open('labeled.json'))
with open('witnesses.txt','w') as f:
 print(len(G),2678-132+1,file=f)
 for g in G:output(f,g['n'],g['k'],g['edges'],g['type'],g['certificate'])
 seen=set()
 for line in open('cover.txt'):
  k,n,i,e,j,h,w,p,q=map(int,line.split())
  need(k not in seen and k>=132 and k<=2678);seen.add(k)
  A,B=G[i],G[j];need(A['type']==B['type']=='P')
  E=[tuple(sorted(x)) for f1,x in enumerate(A['edges']) if f1!=e]
  s,t=A['edges'][e];n0=A['n']
  for step in range(w):
   E.extend([(s,n0),(t,n0+1),(n0,n0+1)]);s,t=n0,n0+1;n0+=2
  E.extend((n0+u,n0+v) for f1,(u,v) in enumerate(B['edges']) if f1!=h)
  a,b=B['edges'][h];E.extend([(s,n0+a),(t,n0+b)]);need(n==n0+B['n'])
  E=sorted(tuple(sorted(x)) for x in E);rot=rotation(n,E);need(rot is not None)
  output(f,n,k,E,'P',rot)
 need(seen==set(range(132,2679)))
print("Literal graphs built:",len(G),"+",len(seen),"planar tail witnesses; max tail host order",
      max(int(s.split()[1]) for s in open('cover.txt')))
