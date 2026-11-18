from itertools import combinations,product
from fractions import Fraction as F
from inputs import arguments,load
args=arguments()
def need(x,msg):
 if not x:raise ArithmeticError(msg)
for n,tot in ((5,2),(6,3),(7,11),(8,147)):
 E=list(combinations(range(n),2));S=list(product((-1,1),repeat=n-1));S=[(1,)+s for s in S];C=[tuple(i for i,(u,v) in enumerate(E) if s[u]!=s[v]) for s in S]
 D=load(n,args); need(set(map(int,D))==set(range(1,tot+1)),'all rows'); keep=[]
 for j,a in D.items():
  need(len(a)==len(E) and all(isinstance(x,int) for x in a),'columns')
  need(max(sum(a[k] for k in c) for c in C)==0,('input valid form',n,j))
  if 0 in a:continue
  for s in S:
   w=[aa*s[u]*s[v] for aa,(u,v) in zip(a,E)]
   if min(w)<=0:continue
   d=[sum(w[k] for k,e in enumerate(E) if u in e) for u in range(n)]
   m=sum(w); c=max(sum(w[k] for k in cut) for cut in C);K=F(sum(abs(sum(x*y for x,y in zip(t,d))) for t in S),len(S))
   gap=15*c-6*m-4*K
   keep.append((int(j),gap,c,m))
   need(gap>=0,('BEKSZ',j,w,d,m,c,K,gap))

 expected={5:(1,F(0),[1]),6:(1,F(5,12),[]),7:(4,F(1,8),[]),8:(29,F(11,32),[])}[n]
 need((len(keep),min(F(v,c) for _,v,c,_ in keep),[j for j,v,c,m in keep if v==0])==expected,('table',n,keep))
 print(n,tot,'full positive orbit count',len(keep),'min normalized slack',str(min(F(v,c) for _,v,c,_ in keep)),'ties',[j for j,v,c,m in keep if v==0])
