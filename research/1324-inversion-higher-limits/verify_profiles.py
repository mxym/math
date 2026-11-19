from itertools import permutations, combinations, product
from functools import lru_cache
from collections import Counter
@lru_cache(None)
def axes(t):
 z=tuple(range(t+4))
 def put(seq,i,x):return seq[:i]+(x,)+seq[i:]
 return [put(put(z,i,'u'),j,'v') for i in range(len(z)+1) for j in range(len(z)+2)]
M=4
REPS=['1324','1243','1342','1432','2341','3421','4321','2143','2413','2431','3412','4231','1234']
def std(p):
 return ''.join(str(sorted(p).index(a)+1) for a in p)
def need(ok):
 if not ok:raise ArithmeticError('failed')
@lru_cache(None)
def skeletal(t):
 a={0,1};b={2+t,3+t};w=set(range(2,t+2)); output=[]
 for x in axes(t):
  for y in axes(t):
   def edge(i,j):return (x.index(i)<x.index(j)) != (y.index(i)<y.index(j))
   if any(edge(i,'u')!=(i in a|w) or edge(i,'v')!=(i in b|w) for i in a|b|w):continue
   e=int(edge('u','v'));ncomp=1 if t or e else 2
   for g in (range(5) if ncomp==2 else (0,)):
    f=int(g==M)
    def macros(axis):
     out=[]
     for i in axis:
      if i==0:out+=['X']
      out.extend([(i,j) for j in range(3 if i in (0,t+2) else 1)])
      if i==t+3:out+=['Y']
     if ncomp==2:
      cut=max(out.index(('u',0)),out.index((1,0)))+1
      out[cut:cut]=[('gap',v) for v in range(g)]
     return out
    xa,ya=macros(x),macros(y)
    output.append((e,g,f,xa,ya))
 return output
@lru_cache(None)
def chunks(p):
 n=len(p)
 # enumerate X and Y positional runs of positive length or None, intervals in values
 ints=[None]+[(i,j) for i in range(n) for j in range(i+1,n+1) if max(map(int,p[i:j]))-min(map(int,p[i:j]))==j-i-1]
 res=set()
 for X,Y in product(ints,repeat=2):
  if X and Y and not X[1]<=Y[0]:continue
  lab=[];val=[]
  Xs=Ys='';j=0
  while j<n:
   if X and j==X[0]:Xs=std(p[j:X[1]]);lab.append('X');val.append(p[j]);j=X[1]
   elif Y and j==Y[0]:Ys=std(p[j:Y[1]]);lab.append('Y');val.append(p[j]);j=Y[1]
   else:lab.append('.');val.append(p[j]);j+=1
  res.add((std(val),''.join(lab),Xs,Ys))
 return sorted(res)
@lru_cache(None)
def rules(p):
 out=[]
 for t in range(5):
  for e,g,f,x,y in skeletal(t):
   pats=set()
   for i in range(1,5):
    for sub in combinations(x,i):
     pats.add((std([y.index(z) for z in sub]),''.join(z if z in ('X','Y') else '.' for z in sub)))
   req={}
   for v in ('1324',p):
    req[v]={(a,b) for pat,lab,a,b in chunks(v) if (pat,lab) in pats}
   out.append((t,e,g,f,req))
 return out
def subsets_positions(p):
 return {std(s) for k in range(1,len(p)+1) for s in combinations(p,k)}|{''}
@lru_cache(None)
def profiles(p):
 # Enumerate ALL abstract masks over the interval-patterns involved in p and 1324.
 # Use necessary conditions only: nonempty endpoint indecomposable avoids 132 (X)
 # or 213 (Y) and has a 21. The whole endpoint cannot itself contain p.
 chunks0=chunks(p)+chunks('1324')
 P=sorted({a for _,_,a,b in chunks0}|{b for _,_,a,b in chunks0}|{'1','21','132','213',p},key=lambda x:(len(x),x))
 def gen(forbid):
  ret=[frozenset([''])]
  required={'','1','21'}
  options=set(P)-required-{forbid,p,'1324'}
  # Do not require profile to be achievable; a superset is useful for zero certification.
  for mask in range(1<<len(options)):
   Q=required|{v for i,v in enumerate(sorted(options)) if mask>>i&1}
   if all(not (subsets_positions(v)&set(P)-Q) for v in Q):ret.append(frozenset(Q))
  return ret
 return gen('132'),gen('213')
def numerator(p,X,Y):
 r=Counter()
 for t,e,g,f,req in rules(p):
  if any(any(u in X and v in Y for u,v in targets) for targets in req.values()):continue
  j=t+e-g
  r[j]+=1
  if not f:r[j-1]-=1
  if t<M:
   r[j+1]-=1
   if not f:r[j]+=1
 return tuple(sorted((a,b) for a,b in r.items() if b))
EXPECTED={
 '1324':{0:9},'1243':{0:16},'1342':{0:36},'1432':{0:25},'2341':{0:36},'3421':{0:36},'4321':{0:25},
 '2143':{0:8,-2:1},'2413':{3:9},'2431':{1:9},'3412':{2:16},'4231':{0:44,1:40,2:16},'1234':{0:36}}
DEG={'2143':0,'2413':0,'2431':1,'3412':1,'4231':2}
EMPTY={'2143':-2,'2413':3,'2431':1,'3412':2,'4231':2}
if __name__=='__main__':
 for p in REPS:
  left,right=profiles(p)
  NN=Counter(numerator(p,x,y) for x,y in product(left,right))
  deg=DEG.get(p,0)
  def poly(a):return ((deg,a),(deg+1,-a)) if a else ()
  need(NN=={poly(a):v for a,v in EXPECTED[p].items()})
  need(numerator(p,frozenset(['']),frozenset(['']))==poly(EMPTY.get(p,0)))
  print(p,len(left),len(right),dict(NN),'empty',EMPTY.get(p,0),flush=True)
 # Inverse and reverse complement preserve inversions and 1324 itself.
 allp={''.join(x) for x in permutations('1234')}
 def inv(p):return ''.join(str(p.index(i)+1) for i in '1234')
 def rc(p):return ''.join(str(5-int(i)) for i in p[::-1])
 orbs=[{p,inv(p),rc(p),rc(inv(p))} for p in REPS]
 need(set.union(*orbs)==allp and sum(map(len,orbs))==24)
 print('All 24 patterns covered by disjoint symmetries; PASS.')
