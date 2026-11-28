#!/usr/bin/env python3
"""Exact pair-distribution replay; Python 3.9+ standard library."""
import math,json,zlib,base64,sys
from fractions import Fraction as Q
import pathlib,hashlib,tarfile,urllib.request,argparse
def add(a,b):return [(a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))]
def scale(a,t): return [x*t for x in a]
def upper(f,lo,hi):
 # Rational Bernstein conversion and exact midpoint subdivision; the final
 # number is a global upper bound, regardless of the stopping tolerance.
 import heapq
 d=len(f)-1;h=hi-lo
 powc=[sum(f[k]*math.comb(k,j)*lo**(k-j)*h**j for k in range(j,d+1))for j in range(d+1)]
 B=[sum(powc[j]*Q(math.comb(i,j),math.comb(d,j))for j in range(i+1))for i in range(d+1)]
 den=math.lcm(*(x.denominator for x in B));a=[int(x*den) for x in B];lower=max(B[0],B[-1]);heap=[];s=0
 def put(v,D):
  nonlocal s
  s+=1;heapq.heappush(heap,(-Q(max(v),D),s,v,D))
 put(a,den)
 for _ in range(10000):
  ub,_,v,D=heapq.heappop(heap);ub=-ub
  if ub<=lower+Q(1,10**10):return ub
  xx=list(v);L=[];R=[]
  for i in range(d+1):
   L.append(xx[0]<<(d-i));R.append(xx[-1]<<(d-i));xx=[u+z for u,z in zip(xx,xx[1:])]
  D<<=d;R.reverse();lower=max(lower,Q(L[-1],D));put(L,D);put(R,D)
 return -heap[0][0]
def product(a,b):
 c=[Q(0)]*(len(a)+len(b)-1)
 for i,z in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=z*v
 return c

NAMES=('dense_0_0.txt','dense_sos1.txt','dense_sos2_1.txt','dense_sos2_2.txt')
DIMS=(13,1,11,10)
def require(t,msg):
 if not t:raise ValueError(msg)
def read_mats(data):
 iv={};mats=[]
 for n,k in zip(NAMES,DIMS):
  v=data['matrices'][n];a=json.loads(zlib.decompress(base64.b64decode(v,validate=True)))
  a=[[(int(l),int(h)) for l,h in row] for row in a]
  require(len(a)==k and all(len(row)==k for row in a),'matrix dimensions')
  require(all(0<=h-l<=2 for row in a for l,h in row),'outward endpoints')
  require(all(a[i][j]==a[j][i]for i in range(k)for j in range(k)),'symmetry')
  iv[n]=a;mats.append([[Q(l,10**24)for l,h in row]for row in a])
 return iv,mats
def source(data,iv,arg):
 # The four raw matrices have very large rational numerators and denominators.
 # Verify inclusions with integers, independently of the rounding that made the snapshot.
 if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
 url='https://github.com/tejasvi/kissing-numbers-lasserre/releases/download/v3/proof_6_76.tgz'
 st=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'sphere-code-certificate-audit'}),timeout=90) if arg=='download' else open(arg,'rb')
 want=dict(data['source_sha256'])
 with st,tarfile.open(fileobj=st,mode='r|gz',bufsize=1048576)as tf:
  for ent in tf:
   n=ent.name.rsplit('/',1)[-1]
   if n not in want:continue
   require(ent.isfile(),'not a regular input');b=tf.extractfile(ent).read()
   require(hashlib.sha256(b).hexdigest()==want.pop(n),'raw source digest: '+n)
   if n in iv:
    ls=b.decode('ascii').splitlines();k=len(iv[n]);rs=[r.split()for r in ls[1:]if r.strip()]
    require(list(map(int,ls[0].split()))==[k,k]and len(rs)==k and all(len(r)==k for r in rs),'source matrix dimensions')
    for i,r in enumerate(rs):
     for j,datum in enumerate(r):
      vals=list(map(int,datum.split('//')));require(len(vals)in(1,2),'rational syntax');p=vals[0];den=vals[1] if len(vals)==2 else 1
      l,h=iv[n][i][j];require(den>0 and l*den<=p*10**24<=h*den,'rational inclusion')
   if not want:break
 require(not want,'missing source files '+str(list(want)))
 print('PASS 12 raw member digests and all 391 rational entries (including both matrix triangles).')
def cert(d,mats,n=76):
 F,aa,X,Y=mats
 th,den,ls,mult,z=d;t=Q(str(th));la=Q(mult,den);z=list(map(lambda a:Q(a,10**7),z));laG=[Q(v,den)for v in ls];q=n*(n-1)//2;eps=Q(2,10**24)
 def mat(v,A,w):return sum(x*y*A[i][j] for i,x in enumerate(v)for j,y in enumerate(w))
 def sos(A):
  u=[Q(0)]
  for i in range(len(A)):
   for j in range(len(A[i])):u=add(u,scale(product(ch[i],ch[j]),A[i][j]))
  return u
 ch=[[1],[0,1]];g=[[1],[0,1]]
 for j in range(1,max(36,len(ls))):g.append(add([0]+scale(g[-1],Q(2*j+4,j+4)),scale(g[-2],Q(-j,j+4))));ch.append(add([0]+scale(ch[-1],2),scale(ch[-2],-1)))
 require(den>0 and len(z)==13 and 0<=len(ls)<=50 and la>=0 and all(a>=0 for a in laG),'dual signs and dimensions')
 r=add(sos(X),product([Q(1,2),Q(-1,2),-1],sos(Y)))
 # Each matrix entry lies between its stored integer lower endpoint and lower+2 units.
 fv=[sum(z[i]*F[i][j]for i in range(13))for j in range(13)]
 f=scale(add(r,scale(fv[2:],2)),la)
 for k,w in enumerate(laG,1):f=add(f,scale(g[k],-w))
 zn=sum(map(abs,z));vn=1+n+11*q
 b=la*(Q(7699,100)-n-n*aa[0][0]+mat(z,F,z)-2*fv[0]-2*n*fv[1]+eps*(zn**2+2*zn*vn+q*221+n)) + sum(laG)*n/2
 # upper() gives rational continuous upper bounds regardless of stopping condition.
 l=min(-upper(scale(f,-1),Q(-1),t),1-upper(scale(f,-1),t,Q(1,2)))
 out=q*l-b
 return out
def cap(t,h):
 # Normalized zonals of S^4; all neighbors above t project to a code with the displayed maximum product.
 g=[[Q(1)],[Q(0),Q(1)]]
 for j in range(1,len(h)):g.append(add([0]+scale(g[-1],Q(2*j+3,j+3)),scale(g[-2],Q(-j,j+3))))
 f=[Q(1)]
 for a,p in zip(h,g[1:]):require(a>=0,'cap sign');f=add(f,scale(p,Q(a,10**6)))
 alpha=(Q(1,2)-t*t)/(1-t*t)
 require(upper(f,Q(-1),alpha)<0,'cap polynomial positivity check')
 return math.floor(Q(1)+sum(Q(a,10**6)for a in h))
def main(data,arg=None):
 iv,mats=read_mats(data)
 if arg:source(data,iv,arg)
 exp=[384,287,259,226,188,143,88,21,14,6,2]
 ts=list(map(Q,['.48','.485','.486','.487','.488','.489','.490','.491','.4911','.4912','.49125']))
 require([Q(d[0])for d in data['thresholds']]==ts,'threshold list')
 for d,b in zip(data['thresholds'],exp):
  x=cert(d,mats);require(math.ceil(x)==b,'claimed count mismatch')
  print('PASS inner product >',d[0],':',b,'unordered pairs')
 caprows=[('.48',[4522618,8390684,8400815,3894426,0,0,366465],26),('.49',[4445041,8177243,8074042,3681148,0,0,347815],25)]
 for s,h,b in caprows:
  require(cap(Q(s),h)==b,'projected degree bound');print('PASS cap degree at',s,':',b)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',metavar='proof_6_76.tgz|download',help='additionally verify the original exact matrices by streaming the local archive, or download from the author');args=ap.parse_args()
 raw=pathlib.Path(__file__).with_name('kissing-six-near-contact-certificate.json').read_bytes()
 require(hashlib.sha256(raw).hexdigest()=='fbfbef5bfac609d60185c7f923f23584fce1423ae0b4bfadcff33681aa8543b0','changed certificate snapshot');main(json.loads(raw),args.source)
