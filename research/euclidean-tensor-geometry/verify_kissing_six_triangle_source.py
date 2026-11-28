#!/usr/bin/env python3
"""Recompute the third-union slack of the original Tomar 6_76 certificate."""
import sys,io,json,hashlib,urllib.request,tarfile,re,itertools,math
from fractions import Fraction as Q
from collections import defaultdict
import pathlib,argparse
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
def require(ok,msg):
 if not ok:raise ValueError(msg)
SCALE=10**34
D={};T={};P={};meta={}
def small(s):return Q(s.decode().replace('//','/'))
def Dmat(f):
 n,m=map(int,f.readline().split());M=[[0]*m for _ in range(n)]
 for i in range(n):
  row=f.readline().split();require(len(row)==m,'source matrix row')
  for j,s in enumerate(row):
   a=s.split(b'//');p=int(a[0]);q=int(a[1])if len(a)>1 else 1;require(q>0,'positive denominator');M[i][j]=p*SCALE//q
 return M
def Tmat(f):
 n,m=map(int,f.readline().split());return [[small(s)for s in f.readline().split()]for i in range(n)]
def polys(f):
 m,n=map(int,f.readline().split())
 def one():
  p={}
  while True:
   l=f.readline().split()
   if not l:break
   e=tuple(map(int,l[1:]));require(len(e)==3,'polynomial dimension');p[e]=small(l[0])
  return p
 return [one()for _ in range(m)],[[one()for j in range(n)]for i in range(m)]
url='https://github.com/tejasvi/kissing-numbers-lasserre/releases/download/v3/proof_6_76.tgz'
def get():
 st=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'sphere-code-certificate-review'}),timeout=150) if archive=='download' else open(archive,'rb')
 with st as r,tarfile.open(fileobj=r,mode='r|gz',bufsize=1<<20)as tf:
  for ent in tf:
   n=ent.name.rsplit('/',1)[-1];mt=re.match(r'(dense_|transform_|poly_3_)sos3_(\d+_\d+)\.txt$',n)
   if not mt:continue
   prefix,k=mt.groups();b=tf.extractfile(ent).read();meta[n]=hashlib.sha256(b).hexdigest()
   if expected['source_sha256'].get(n)!=meta[n]:raise ValueError('changed raw source member: '+n)
   dest,read=(D,Dmat)if prefix=='dense_'else((T,Tmat)if prefix=='transform_'else(P,polys));dest[k]=read(io.BytesIO(b))
   if len(D)==len(T)==len(P)==15:break
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ap=argparse.ArgumentParser(description='Independently reconstruct the exact interval snapshot for the 15 triangular SOS blocks.')
ap.add_argument('archive',help='path to proof_6_76.tgz, or download to stream from the author');archive=ap.parse_args().archive
expected=json.loads(pathlib.Path(__file__).with_name('kissing-six-coupled-triple-data.json').read_text())
get()
if meta!=expected['source_sha256'] or len(meta)!=45:raise ValueError('different source file inventory')
R=defaultdict(Q);loss=Q(0)
for k,(pref,vs)in sorted(P.items()):
 A=D[k];T0=T[k];n=len(A);require(all(len(r)==n for r in A)and all(len(r)==n for r in T0), "transformed matrix dimensions")
 for w,rows in zip(pref,vs):
  require(len(rows)==len(T0),'basis dimension');ids=sorted(set().union(*(r.keys()for r in rows)));emap={v:i for i,v in enumerate(ids)}
  coeff=[[Q(0)]*len(ids)for i in range(n)]
  for r,tr in zip(rows,T0):
   for i,t in enumerate(tr):
    if t:
     for e,v in r.items():coeff[i][emap[e]]+=t*v
  den=math.lcm(*(v.denominator for row in coeff for v in row));M=[[int(den*v)for v in row]for row in coeff]
  loss+=sum(map(abs,w.values()))*(sum(abs(v)for row in M for v in row)**2)/Q(SCALE*den**2)
  cols=[[(i,M[i][j])for i in range(n)if M[i][j]]for j in range(len(ids))]
  AM=[[sum(a[i]*v for i,v in col)for col in cols]for a in A];rr=defaultdict(int)
  for i,e in enumerate(ids):
   for j,u in enumerate(ids[:i+1]):
    rr[tuple(x+y for x,y in zip(e,u))]+=sum(v*AM[l][j]for l,v in cols[i])*(1 if i==j else 2)
  for u,c in rr.items():
   if c:
    c=Q(c,SCALE*den**2)
    for e,z in w.items():R[tuple(x+y for x,y in zip(e,u))]+=z*c
 print('PASS source block',k,flush=True)
# Average over permutations before rounding. The actual 3-slack is symmetric by the union identity.
E=defaultdict(Q)
for e,v in R.items():
 for perm in itertools.permutations(e):E[perm]+=v/6
fac=10**26;zp={e:v.numerator*fac//v.denominator for e,v in E.items()};loss+=Q(len(E),fac);out=[[int(i),int(j),int(k),str(v)]for(i,j,k),v in sorted(zp.items())if i<=j<=k and v]
import base64,zlib
actual=json.loads(zlib.decompress(base64.b64decode(expected['triangle_coefficients'])))
require(out==actual,'coefficient snapshot mismatch')
require(loss<=Q(2,10**23),'error budget exceeded')
print('PASS 45 original files, 15 exact outward block calculations,',len(out),'stored symmetric coefficients; uniform error <= 2e-23.')
