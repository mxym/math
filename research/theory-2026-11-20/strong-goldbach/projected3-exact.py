import sys,itertools,collections,hashlib
from math import gcd,lcm
from functools import reduce
import sympy as s
cnt=collections.Counter(); results=[];term=[];audit=[];x=s.symbols('x')
def ints(y):
 d=lcm(*(int(q.q) for q in y));u=[int(d*q) for q in y];g=reduce(gcd,map(abs,u));return [i//g for i in u]
def signcheck(A):
 B=-A.copy()
 for i in range(5):B[i+1,i]+=1
 return any(all(int(q)%2 for q in B*s.Matrix(u)) for u in itertools.product(range(2),repeat=5))
def inj(w,v):
 D=lcm(*(int(a.q) for a in w)); W=[int(t*D) for t in w];seen=set()
 def go(i,z,k):
  if i==5:
   if k in seen:return False
   seen.add(k);return True
  for j in range((D-1-z)//W[i]+1):
   if not go(i+1,z+j*W[i],k+j*v[i]):return False
  return True
 return go(0,0,0)
def ch(sol):return ' '.join(map(str,sol))
for raw in sys.stdin:
 z=raw.split()
 if not z:continue
 v=[0]+list(map(int,z[6:]));A=s.Matrix([[int(a) for a in row] for row in z[:6]]);B=-A.copy()
 for i in range(5):B[i+1,i]+=1
 cnt['input']+=1; l0=A.T.nullspace()
 if len(l0)!=1:continue
 l=ints(l0[0])
 if sum(l):continue
 w=list(s.linsolve((A,s.ones(6,1))))[0]
 if not all(0<k<1 for k in w):continue
 cnt['weight']+=1
 if sum(1 for t in w if 2*t<=1)<3:continue
 cnt['halves']+=1
 if not inj(w,v[1:]):continue
 cnt['injective']+=1
 C0=B.T.nullspace()
 if len(C0)!=2:continue
 C=s.Matrix([ints(a) for a in C0]);N=C.col_join(C*s.diag(*v)).nullspace()
 if len(N)!=2:continue
 H=[u*x+y for u,y in zip(*[ints(a) for a in N])]
 if not all(H):continue
 cnt['line']+=1;D=lcm(*(int(t.q) for t in w))
 bad=False
 for j in range(6):
  vec=C[1,j]*C.row(0)-C[0,j]*C.row(1)
  ii=[i for i in range(6) if vec[i]]
  if ii and max(v[i] for i in ii)-min(v[i] for i in ii)<D:bad=True
 if bad:continue
 cnt['span']+=1;term.append(' '.join(z));sg=signcheck(A)
 f=s.Poly(s.prod(H[i]**li for i,li in enumerate(l) if li>0)-s.prod(H[i]**(-li) for i,li in enumerate(l) if li<0),x)
 if f.is_zero:
  # Independently require that every eigenspace row has >=2 entries of each sign.
  witness=None
  for j in range(6):
   row=list(C[1,j]*C.row(0)-C[0,j]*C.row(1))
   if any(row) and min(sum(t>0 for t in map(int,row)),sum(t<0 for t in map(int,row)))<2:witness=row
  if witness is None and sg:raise RuntimeError(('unaudited identically zero product',z))
  cnt['identity']+=1;audit.append(('identity',z,sg,witness));continue
 kval=int(sum(A.row(0)));P=s.Poly(s.prod(H[i+1]**int(A[0,i]) for i in range(5)),x);Q=s.Poly(H[0]**kval,x);values=[]
 for g,m in f.factor_list()[1]:
  if any(s.rem(s.Poly(h,x),g).is_zero for h in H):continue
  val=(P*s.invert(Q,g)).rem(g)
  if val.degree()<=0:values.append(val.nth(0))
 hi=[s.Poly(h,x).nth(1) for h in H]
 if all(hi) and s.prod(hi[i]**li for i,li in enumerate(l))==1:
  values.append(s.prod(hi[i+1]**int(A[0,i]) for i in range(5))/hi[0]**kval)
 for y in set(values):
  if y.is_Integer and y<-1:
   fs=s.factorint(-y)
   if len(fs)!=1:continue
   pp,ee=list(fs.items())[0]
   if ee!=kval-1 or pp==2:continue
   cnt['seed']+=1;audit.append(('seed',z,int(pp),sg))
   if sg:results.append((int(pp),z))
print(dict(sorted(cnt.items())));print('canonical terminal SHA256',hashlib.sha256(('\n'.join(sorted(term))+'\n').encode()).hexdigest())
for y in audit:print(*y)
print('survivors',results)
if results:sys.exit(2)

