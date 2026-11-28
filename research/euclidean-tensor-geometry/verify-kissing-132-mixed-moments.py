#!/usr/bin/env python3
"""Exact proof replay. Only the Python standard library is needed here."""
import sys,math,base64,zlib,json,hashlib,itertools
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O; exact assertions must be active')
from fractions import Fraction as Q
from functools import reduce
def add(a,b):return [(a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))]
def scale(a,t): return [x*t for x in a]
def upper(f,lo,hi,n):
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
from functools import lru_cache
def product(a,b):
 c=[Q(0)]*(len(a)+len(b)-1)
 for i,z in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=z*v
 return c
@lru_cache(None)
def transferpotential(q,q0):
 rr=SRC[str(q0)];cc=json.loads(zlib.decompress(base64.b64decode(rr[-1])));d,D=cc[2:4];ee=Q(q0-2,q-2);J=[Q(0)]
 cheb=[[Q(1)],[Q(0),Q(1)]]
 for j in range(2,d+1):cheb.append(add([Q(0)]+scale(cheb[-1],Q(2)),scale(cheb[-2],Q(-1))))
 z=[Q(1)];c111=Q(0)
 for k,M in enumerate(cc[7]):
  ab=[Q(0)]
  for j in range(len(M[0])):
   phi=[Q(0)]
   for i,row in enumerate(M):phi=add(phi,scale(cheb[i],Q(row[j],D)))
   ab=add(ab,product(phi,phi))
   if k==0:
    v=sum(phi);c111+=v*v;J=add(J,scale(phi,2*v))
  J=add(J,product(z,ab));z=product(z,[Q(1),Q(0),Q(-1)])
 p=add([0,0,Q(-1,4),0,Q(1)],scale(J,1-ee));g=[[Q(1)],[Q(0),Q(1)]]
 for k,v in enumerate(cc[4],1):
  if len(g)<=k:
   j=k-1;g.append(add([Q(0)]+scale(g[-1],Q(2*j+5,j+5)),scale(g[-2],Q(-j,j+5))))
  if v:p=add(p,scale(g[k],Q(v,D)))
 hn=Q(sum(cc[4]),D);B=(Q(rr[3])-Q(3,4)-hn-c111)/(q0-1)
 rhs=(Q(3,4)+hn+(3-2*ee)*c111+(q-1)*B)/q
 p[0]-=rhs
 return p
def go(X,w,n=2048):
 sizes=X['sizes'];C=X['counts'];D=X['D'];K=len(sizes);ord=len(X['fac'])
 if not (type(D)is int and D>0 and sizes==sorted(set(sizes)) and all(type(j)is int and j>=5 for j in sizes) and len(C)==len(X['lambda'])==K and all(type(c)is int and c>0 for c in C)):raise ValueError('invalid component sizes or scale')
 if not (1<=ord<=32 and ord==len(X['contrast'])):raise ValueError('invalid harmonic block count')
 if X.get('g7') and ord<10:raise ValueError('missing degree ten')
 if set(map(int,X.get('tangent',{})))-set(sizes) or any(row[0]not in sizes for row in X.get('transfers',[])+X.get('mixedCones',[])):raise ValueError('unused local row')
 for mat,dd in zip(X['fac'],X['contrast']):
  if len(mat)!=K or len(dd)!=K or not mat[0] or any(len(row)!=len(mat[0]) for row in mat) or any(type(v)is not int for row in mat for v in row) or any(type(v)is not int or v<0 for v in dd):raise ValueError('malformed Gram block')
 g=[[Q(1)],[Q(0),Q(1)]]
 for j in range(1,ord):g.append(add([Q(0)]+scale(g[j],Q(2*j+5,j+5)),scale(g[j-1],Q(-j,j+5))))
 output=Q(0);largest=[]
 for i in range(K):
  for u in range(i,K):
   for same in ([True,False]if i==u and C[i]>1 else [i==u]):
    F=[Q(0)];L=Q(X['lambda'][i],D)if same else Q(0)
    if L<0:raise ValueError('negative scalar')
    for k,(fac,di)in enumerate(zip(X['fac'],X['contrast']),1):
     if any(x<0 for x in di):raise ValueError('indefinite contrast')
     a=Q(sum(x*y for x,y in zip(fac[i],fac[u])),D*D)
     if i==u:a+=Q(di[i],D*D)*(int(same)-Q(1,C[i]))
     F=add(F,scale(g[k],a))
    if same:
     cap=Q(10**6,w[str(sizes[i])]);d=Q(1,sizes[i]);dh=min(Q(1),(64*cap+1)/49)if sizes[i]in (5,7,9)else d
     poly=add(F,[0,0,L/4,0,-L]);price=L*cap
     if sizes[i]==7 and X.get('g7',False):
      cap=Q(180,1000);dh=min(Q(1),(cap+Q(21,1000))/Q(771,1000));poly=list(F)
      for kk,ww in [(2,9),(4,17),(10,10)]:poly=add(poly,scale(g[kk],-L*Q(ww,48)))
      price=L*cap
     if str(sizes[i]) in X.get('tangent',{}):
      q=sizes[i];ll,zz=X['tangent'][str(q)];ell=Q(ll,D);z=[Q(v,D) for v in zz];assert ell>0
      rr=SRC[str(q)];cc=json.loads(zlib.decompress(base64.b64decode(rr[-1])));d0,D0=cc[2:4]
      cf=cc[7][0];cheb=[[Q(1)],[Q(0),Q(1)]]
      for j in range(2,d0+1):cheb.append(add([Q(0)]+scale(cheb[-1],Q(2)),scale(cheb[-2],Q(-1))))
      assert len(z)==len(cf[0]);poly=add(poly,[0,0,ell/4,0,-ell])
      for j,val in enumerate(cc[4],1):
       if val:
        while len(g)<=j:
         u0=len(g)-1;g.append(add([Q(0)]+scale(g[-1],Q(2*u0+5,u0+5)),scale(g[-2],Q(-u0,u0+5))))
        poly=add(poly,scale(g[j],-ell*Q(val,D0)))
      for j,row in enumerate(cf):
       poly=add(poly,scale(cheb[j],-2*q*sum(t*Q(v,D0) for t,v in zip(z,row))))
      price+=ell*Q(rr[3])/q+q*sum(t*t for t in z)/ell
     for qq,q0,ll,zz in X.get('mixedCones',[]):
      if qq!=sizes[i]:continue
      assert ll>0 and qq>=11 and q0>=3
      ell=Q(ll,D);z=[Q(v,D) for v in zz];ee=Q(q0-2,qq-2);poly=add(poly,scale(transferpotential(qq,q0),-ell))
      rr=SRC[str(q0)];cc=json.loads(zlib.decompress(base64.b64decode(rr[-1])));cf=cc[7][0];ch=[[Q(1)],[Q(0),Q(1)]]
      assert len(z)==len(cf[0])
      for j in range(2,len(cf)):ch.append(add([0]+scale(ch[-1],Q(2)),scale(ch[-2],-1)))
      for j,row in enumerate(cf):
       poly=add(poly,scale(ch[j],-2*qq*ee*sum(t*Q(v,cc[3])for t,v in zip(z,row))))
      price+=qq*ee*sum(t*t for t in z)/ell
     for qq,q0,ww in X.get('transfers',[]):
      assert ww>=0 and qq>=11 and q0>=3
      if qq==sizes[i]:poly=add(poly,scale(transferpotential(qq,q0),-Q(ww,D)))
     at=sum(poly);b=upper(poly,Q(-1),Q(1,2),n)if d!=1 else Q(0)
     value=C[i]*(price+max(d*at+(1-d)*b,dh*at+(1-dh)*b))
    else:
     b=upper(F,Q(-1,2),Q(1,2),n);value=C[i]*(C[u]-(i==u))*(2 if i!=u else 1)*b
    output+=value
 return output


def cover_budget(W):
 # Delete a canonical barrier, then double its surviving singletons.
 # One isolated antipodal pair costs w_1; a nontrivial odd k costs w_k.
 H=10**18;dp=[[H]*132 for i in range(132)];dp[0][0]=0
 items=[(2,1,W[1])]+[(k,(k+1)//2,W[k])for k in range(5,132,2)]
 for n in range(132):
  for b in range(n+1):
   cur=dp[n][b]
   if cur==H:continue
   for k,e,w in items:
    if n+k<=131:dp[n+k][b+e]=min(dp[n+k][b+e],cur+w)
 best=min(x for row in dp for x in row[70:])
 if best!=84017101 or best<=84000000:raise RuntimeError('different universal budget: '+str(best))
 return best

def run(read,only=None):
 global SRC
 note=json.loads(read('kissing-132-mixed-inputs.json'));W=note['weights'];SRC=note['charts']
 expected=[5,7,9,31,33,37,81,91]
 ancestor=read('kissing-131-component-data.json')
 if hashlib.sha256(ancestor.encode()).hexdigest()!='aa87dd64216b973c04512517b8a844dbeeba95b224c5261808f2361171c60e0e':raise RuntimeError('changed predecessor charge table')
 ww=json.loads(ancestor)['weights'][:]
 for q,t in [(5,250950),(7,201000),(9,161000)]:ww[q]=max(ww[q],10**12//t)
 for q in expected[3:]:ww[q]=max(ww[q],10**12*q//SRC[str(q)][1])
 if W!=ww or len(W)!=133:raise RuntimeError('unverified charge vector')
 libsource=read('verify-kissing-component-measure.py')
 if hashlib.sha256(libsource.encode()).hexdigest()!='b24478aa381465e7708feba99fa13ebc0ba99b0f2aa8379aa4e0a4ef2e2db718':raise RuntimeError('changed predecessor labeled verifier')
 env={'__name__':'pinned_component_verifier'};exec(compile(libsource,'pinned_component_verifier','exec'),env)
 # Uniform lower bound for the alternative pair potential, and its weak-interval maximum.
 gg=[[Q(1)],[Q(0),Q(1)]]
 for k in range(1,10):gg.append(add([Q(0)]+scale(gg[-1],Q(2*k+5,k+5)),scale(gg[-2],Q(-k,k+5))))
 G=[Q(0)]
 for k,v in [(2,9),(4,17),(10,10)]:G=add(G,scale(gg[k],Q(v,48)))
 if sum(G)!=Q(3,4) or upper(scale(G,-1),Q(-1),Q(1,2),0)>Q(21,1000) or upper(G,Q(-1,2),Q(1,2),0)>Q(-1,100):raise ArithmeticError('auxiliary scalar bounds')
 bad={p for p in env['residual'](W,132,63) if len(p)==8 and sum(p)==132 and min(p)>=5}
 if len(bad)!=275 or min(sum(W[x]for x in p)for p in bad)!=83722101:raise ArithmeticError('different scalar census')
 rules=set();vals=[]
 def receive(p,value):
  if p in rules or p not in bad or value>=0:raise ArithmeticError(('failed or duplicated shape',p,value))
  rules.add(p);vals.append(value)
 if only is None or only==0:
  o=json.loads(read('kissing-132-inherited-templates.json'));T=[env['Template'](b)for b in o['templates']]
  for parts,k,mp,v in o['rules']:
   p=tuple(parts);ss=sorted(set(p));cc=[p.count(i)for i in ss]
   assert 0<=k<len(T) and len(mp)==len(v)==len(ss) and all(0<=j<T[k].N for j in mp) and all(type(x)is int and x>=0 for x in v)
   receive(p,T[k].check(ss,cc,mp,v,W))
  if len(o['rules'])!=57:raise ArithmeticError('wrong inherited count')
  print('PASS 57 inherited mapped certificates',flush=True)
 for j in range(1,5):
  if only is not None and only!=j:continue
  rows=json.loads(read('kissing-132-direct-'+str(j)+'.json'))
  for part,b in rows:
   p=tuple(part);X=json.loads(zlib.decompress(base64.b64decode(b,validate=True)))
   if list(p)!=sorted(v for s,n in zip(X['sizes'],X['counts'])for v in [s]*n):raise ArithmeticError('wrong partition')
   receive(p,go(X,{str(i):w for i,w in enumerate(W)}))
  print('PASS direct block',j,len(rows),flush=True)
 if only is None and rules!=bad:raise ArithmeticError(('incomplete shape coverage',len(rules),len(bad)))
 print('PASS strictly negative rational majorants:',len(rules),'; universal 70-part minimum charge below 132 points:',cover_budget(W),flush=True)
if __name__=='__main__':
 root=Path(__file__).resolve().parent
 run(lambda s:(root/s).read_text(encoding='utf-8'),int(sys.argv[1])if len(sys.argv)>1 else None)
