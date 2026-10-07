#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from random import Random
import json
ROOT=Path(__file__).resolve().parents[1]/"results"
ROOT.mkdir(exist_ok=True)
rng=Random(2026100710)
def cross(o,a,b):return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def hull(points):
 p=sorted(set(points));lo=[];hi=[]
 for x in p:
  while len(lo)>=2 and cross(lo[-2],lo[-1],x)<=0:lo.pop()
  lo.append(x)
 for x in reversed(p):
  while len(hi)>=2 and cross(hi[-2],hi[-1],x)<=0:hi.pop()
  hi.append(x)
 return lo[:-1]+hi[:-1]
def det2(a,b):return a[0]*b[1]-a[1]*b[0]
def det3(a,b,c):return a[2]*det2(b,c)-b[2]*det2(a,c)+c[2]*det2(a,b)
out=[]
for i in range(200):
 verts=hull([(rng.randrange(-20,21),rng.randrange(-20,21)) for _ in range(8+i%17)])
 z=tuple(sum(F(x[j]) for x in verts)/len(verts) for j in range(2));v=[tuple(F(x[j])-z[j] for j in range(2)) for x in verts]
 area=sum(det2(x,v[(j+1)%len(v)]) for j,x in enumerate(v))/2;facets=[]
 for j,x in enumerate(v):
  y=v[(j+1)%len(v)];u=(y[1]-x[1],x[0]-y[0]);b=sum(a*c for a,c in zip(u,x));facets.append((*u,b))
 P=sum(abs(det2(a,b)) for a,b in combinations(facets,2));S=sum(abs(det3(a,b,c)) for a,b,c in combinations(facets,3));signed=sum(det3(a,b,c) for a,b,c in combinations(facets,3))
 if S!=signed or S!=4*area**2:raise RuntimeError('Planar lifted identity failed')
 R=P/area;a=S/(2*area*P);e=a-F(1,3);rho=1-R/6
 if a*R!=2 or rho!=3*e/(1+3*e):raise RuntimeError('Planar ratio conversion failed')
 out.append({'vertices':len(v),'area':str(area),'P':str(P),'S':str(S),'R':str(R),'a':str(a)})
(ROOT/'planar_identity_results.json').write_text(json.dumps({'cases':out,'count':len(out),'status':'PASS'},indent=2)+'\n');print('PASS: 200 exact convex-polygon identities and deficit conversions.')
