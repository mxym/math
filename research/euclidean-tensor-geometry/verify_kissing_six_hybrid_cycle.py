#!/usr/bin/env python3
"""Exact solver-free replay: signed quartic cube minors and continuous C7 Gram-tree duals. Standard library."""
import sys,itertools,math,json,zlib,base64,pathlib,hashlib,heapq
from fractions import Fraction as Q
def require(ok,msg):
 if not ok:raise ValueError(msg)
K=4096;den=4*K**4;F0=600;H0=den*F0**2
E=list(itertools.combinations(range(7),2));eid={e:i for i,e in enumerate(E)}
F=Q
# Each rational matrix minorizes the summed quartic deficiency throughout the cube.
D=10**6;H=[]
def ldl(A):
 if not A:return []
 p=A[0][0];require(p>0,'nonpositive pivot')
 a=[r[0]for r in A[1:]];return [(p,a)]+ldl([[A[i+1][j+1]-x*y/p for j,y in enumerate(a)]for i,x in enumerate(a)])
def quadratic_inv(A,y):
 ans=0
 for p,col in ldl(A):
  z=y[0];ans+=z*z/p;y=[b-z*c/p for b,c in zip(y[1:],col)]
 return ans
def verify_cube():
 alpha=(5+min(H[i][i]for i in range(7)))/6;require(alpha>0,'second derivative cutoff')
 ldl([[H[i][j]+F(21,10)*(i==j)for j in range(7)]for i in range(7)])
 for e in itertools.product((-1,0,1),repeat=7):
  S=[i for i in range(7)if not e[i]];B=[i for i in range(7)if e[i]]
  A=[[alpha*(i==j)-H[i][j] for j in S]for i in S];u=[sum(H[i][j]*e[j]for j in B)for i in S]
  require(sum(e[i]*e[j]*H[i][j]for i in B for j in B)+quadratic_inv(A,u)<=0,'failed ternary face '+str(e))
 print('PASS 2187 exact Schur faces',flush=True)
def rounded_polys(matrices,W,w):
 # Independently polarize direct trace evaluations at integral test matrices.
 from itertools import combinations_with_replacement as cwr
 J=list(cwr(range(21),2));where={p:i for i,p in enumerate(J)};rows=set();D=10**6;P=10**9
 for mat in matrices:
  def value(ts):
   S=[[int(i==j)for j in range(7)]for i in range(7)]
   for e,v in ts:
    i,j=E[e];S[i][j]=S[j][i]=v
   A=[[sum(mat[i][k]*S[k][j]for k in range(7))for j in range(7)]for i in range(7)]
   L=sum(A[i][i]for i in range(7));M=sum(A[i][j]*S[j][i]for i in range(7)for j in range(7));N=sum(A[i][j]*A[j][i]for i in range(7)for j in range(7))
   return -W*L/(84*w*D)+Q(M,98*D)+Q(5*(6*N-L**2),168*49*D**2)
  c=value([]);up=[value([(i,1)])for i in range(21)];dn=[value([(i,-1)])for i in range(21)]
  co=[c]+[(x-y)/2 for x,y in zip(up,dn)]+[(up[i]+dn[i])/2-c if i==j else value([(i,1),(j,1)])-up[i]-up[j]+c for i,j in J]
  base=[int((x*P)//1)for x in co];base[0]+=len(base)
  for h in range(7):
   for s in (-1,1):
    t=[(h+s*i)%7 for i in range(7)];p=[eid[tuple(sorted((t[i],t[j])))]for i,j in E]
    rows.add(tuple([base[0]]+[base[1+i]for i in p]+[base[22+where[tuple(sorted((p[i],p[j])))]]for i,j in J]))
 return sorted(rows)
def support(row,lo,hi,z):
 # Upper-bound every signed scaled quadratic by an affine expression. For a
 # mixed monomial an affine-minus-bilinear attains its minimum at a corner.
 aa=[K*x for x in row[1:22]];cc=K*K*row[0]
 for c,(i,j)in zip(row[22:],itertools.combinations_with_replacement(range(21),2)):
  if not c:continue
  if i==j:
   a,b=(hi[i],lo[i])if c>0 else(z[i],z[i])
  else:
   v=((hi[i],lo[j]),(lo[i],hi[j]))if c>0 else((lo[i],lo[j]),(hi[i],hi[j]))
   a,b=min(v,key=lambda v:c*(v[0]*z[j]+v[1]*z[i]-v[0]*v[1]))
   require(all(c*(a*y+b*x-a*b-x*y)>=0 for x in (lo[i],hi[i])for y in (lo[j],hi[j])),'invalid mixed envelope')
  aa[i]+=c*b;aa[j]+=c*a;cc-=c*a*b
 return cc,aa
def replay(data):
 global H
 tar=data['target'];sym=data['sym'];masses=data['masses'];psd=data['psd'];tree=data['tree'];n=7
 W=Q(data['W0']);w=Q(4975124,10**6);require(W==Q(47952827,10**6) and tar==199095,'different claimed theorem');require(W>=Q(47868660,10**6)and W<48,'ineligible nominal charge')
 require(W/24-1-Q(21,10)*w/12>0 and Q(tar,10**6)<min(1/(w+48-W),1/w+(W**2/48-W)/w**2),'insufficient contradiction margin')
 for j,mat in enumerate(data['kernels']):
  require(len(mat)==7 and all(len(r)==7 and all(type(i)is int for i in r)for r in mat),'kernel dimensions')
  H=[[Q(i,10**6)for i in r]for r in mat];require(all(H[i][j]==H[j][i]for i in range(7)for j in range(7)),'kernel symmetry');verify_cube()
 rowsJ=rounded_polys(data['kernels'],W,w);isedge=[(i-j)%7 in (1,6)for i,j in E]
 # Take lexicographically maximal strong-then-weak ordered Gram entries under graph automorphisms.
 autos=[]
 for p in itertools.permutations(range(n)):
  m=tuple(eid[tuple(sorted((p[i],p[j])))]for i,j in E)
  if all(isedge[i]==isedge[j]for i,j in enumerate(m)):autos.append(m)
 valid=set()
 for i in sorted(range(21),key=lambda i:not isedge[i]):
  valid.update((i,p[i])for p in autos if p[i]!=i);autos=[p for p in autos if p[i]==i]
 require(len(sym)==len(valid)and set(map(tuple,sym))==valid,'orbit-order inequalities')
 for w in masses:require(len(w)==7 and sum(w)==F0 and all(type(x)is int and x>=0 for x in w),'probability weights')
 for v in psd:require(len(v)==7 and any(v)and all(type(x)is int for x in v),'Gram direction')
 def tighten(lo,hi):
  T=[[-K]*(2*n)for _ in range(2*n)]
  for i in range(2*n):T[i][i]=K
  for j,(a,b)in enumerate(E):
   T[a][b]=T[b][a]=T[n+a][n+b]=T[n+b][n+a]=lo[j]
   T[a][n+b]=T[n+b][a]=T[b][n+a]=T[n+a][b]=-hi[j]
  for i in range(2*n):
   row=T[i].copy()
   for a in range(2*n):
    for b in range(a):
     x,y=row[a],row[b]
     if x+y>=0:
      zz=(K*K-x*x)*(K*K-y*y);r=math.isqrt(zz);r+=r*r<zz
      t=(x*y-r)//K;T[a][b]=T[b][a]=max(T[a][b],t)
  lo=[T[a][b]for a,b in E];hi=[-T[a][n+b]for a,b in E]
  if any(T[a][n+a]>-K for a in range(n)):return None
  for _ in range(2):
   for i,j in sym:lo[i]=max(lo[i],lo[j]);hi[j]=min(hi[j],hi[i])
  return None if any(x>y for x,y in zip(lo,hi))else(lo,hi)
 # The producer used affine majorants. This verifier instead bounds the
 # combined univariate quartic directly, independently on every edge.
 def bern(w,v,l,h):
  def f(y):return w*(4*y**4-K*K*y*y)+v*y
  def fp(y):return w*(16*y**3-2*K*K*y)+v
  d=h-l;a=12*f(l);b=12*f(h)
  return [a,a+3*d*fp(l),a+6*d*fp(l)+d*d*w*(48*l*l-2*K*K),b-3*d*fp(h),b]
 def halves(u):
  l=[];r=[]
  while len(u)>1:
   l.append(u[0]);r.append(u[-1]);u=[(a+b+1)//2 for a,b in zip(u,u[1:])]
  return (l+u,u+r[::-1])
 maxsplit=0
 def checkdual(lo,hi,rows):
  nonlocal maxsplit
  wco=[0]*21;gco=[0]*21;gc=diag=tw=kt=kc=0;ka=[0]*21;M0=49*10**9*K*K
  for row in rows:
   kind,idx,t=row[:3]
   t=int(t);require(t>0 and type(idx)is int and idx>=0,'dual multiplier')
   if kind==0:
    w=masses[idx];tw+=t;diag+=t*sum(c*c for c in w)
    for e,(i,j)in enumerate(E):wco[e]+=2*t*w[i]*w[j]
   elif kind==1:
    i,j=sym[idx];gco[i]+=t;gco[j]-=t
   elif kind==2:
    v=psd[idx];gc+=t*sum(x*x for x in v)
    for e,(i,j)in enumerate(E):gco[e]+=2*t*v[i]*v[j]
   else:
    require(kind==3 and len(row)==4,'test type');anchor=row[3];require(len(anchor)==21 and all(type(z)is int and lo[a]<=z<=hi[a]for a,z in enumerate(anchor)),'invalid tangent anchor')
    c,a=support(rowsJ[idx],lo,hi,anchor);kt+=t;kc+=t*c
    for e in range(21):ka[e]+=t*a[e]
  tw+=kt;const=12*((diag*(3*den//4)+gc*H0)*M0+(3*H0*M0//28)*kt+49*H0*kc);heaps=[];low=[];serial=0
  for wc,vc,ac,l,h in zip(wco,gco,ka,lo,hi):
   B=bern(M0*wc+2*(M0//49)*F0**2*kt,M0*vc*(H0//K)+49*H0*ac,l,h);heaps.append([(-max(B),serial,B)]);serial+=1;low.append(max(B[0],B[-1]))
  # These lower references only choose a coordinate for subdivision; only the
  # upper coefficient bounds enter the accepting condition.
  for it in range(4096):
   ub=[-h[0][0]for h in heaps];total=const+sum(ub)
   if (total*10**6<=12*tar*tw*H0*M0)if tw else(total<0):
    maxsplit=max(maxsplit,it);return
   i=max(range(21),key=lambda j:ub[j]-low[j]);require(ub[i]>low[i],'false certificate')
   _,_,row=heapq.heappop(heaps[i])
   for B in halves(row):
    heapq.heappush(heaps[i],(-max(B),serial,B));serial+=1
    # Selection heuristic only: these lower references may round upward.
    low[i]=max(low[i],B[0],B[-1])
  raise ValueError('unresolved mixed quartic')
 pos=0;de=0;leaf=0
 def go(lo,hi,d):
  nonlocal pos,de,leaf
  require(pos<len(tree)and d<110,'truncated or unbounded certificate');cell=tree[pos];pos+=1;de=max(de,d);bounds=tighten(lo,hi)
  if cell==['X']:require(bounds is None,'invalid empty cell');return
  require(bounds is not None,'closure in a differently tightened cell');lo,hi=bounds
  if cell[0]=='D':
   checkdual(lo,hi,cell[1]);leaf+=1;return
  i,t=cell;require(type(i)is int and 0<=i<21 and type(t)is int and lo[i]<t<hi[i],'invalid split')
  z=hi.copy();z[i]=t;go(lo,z,d+1);z=lo.copy();z[i]=t;go(z,hi,d+1)
 go([-K if s else -K//2 for s in isedge],[-K//2 if s else K//2 for s in isedge],0)
 require(pos==len(tree),'unused tree nodes');print('PASS hybrid C7; W0',W,'target',tar,'nodes',pos,'dual leaves',leaf,'depth',de,'univariate refinements at most',maxsplit,flush=True)
if __name__=='__main__':
 path=pathlib.Path(__file__).with_name('kissing-six-hybrid-cycle-cert.json');data=json.loads(path.read_text());s=data['tree'];require(hashlib.sha256(s.encode()).hexdigest()=='cbb46885bdb251e04038247658fde71b4d9d4ff59f423f1961907be62c17c499','different frozen witnesses');replay(json.loads(zlib.decompress(base64.b64decode(s))))
