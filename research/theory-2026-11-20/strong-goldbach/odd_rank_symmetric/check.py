"""Exact synthetic log profiles and sign bookkeeping; also valid with python -O."""
def need(t,m):
 if not t:raise ValueError(m)
def comps(n,k,lo=1):
 if k==1:
  if n>=lo:yield (n,)
  return
 for i in range(lo,n//k+1):
  for z in comps(n-i,k-1,i):yield (i,)+z
def score(t,A,D):
 L=sum(t);terms=[(0,1)]
 for u in t:terms+=[(s+u,-v) for s,v in terms]
 F=sum(sgn*(L-(s if s<=A else 0)) for s,sgn in terms if s<=D)
 H=-L*sum(sgn for s,sgn in terms if 2*s<L)
 K=-F
 seam=any(D<s and 2*s<L for s,sgn in terms)
 return K,H,seam
n=0
for t in ((u,41-u) for u in range(1,21)):
 A,D=3,18
 k,h,seam=score(t,A,D)
 r,s=t
 expected=-r if r<=A else 0 if r<=D else -41
 need(k==expected and not h,'rank two')
for rank in range(2,9):
 for t in comps(39,rank):
  for A,D in [(1,18),(2,17)]:
   k,h,seam=score(t,A,D)
   if not rank%2:need(h==0,'complement pairs')
   if rank==3:need(h==(78 if 2*t[-1]<39 else 0),'triple')
   if not seam:need(abs(k-h)<=2**rank*A,'seam')
   n+=1
# Opposing bounded odd signs remain: balanced ranks three and five.
need(score((7,7,7),1,9)[1]>0 and score((5,5,5,5,5),1,11)[1]<0,'adverse 3 by 5')
def corr(a,b):return sum(x*y for x,y in zip(a,reversed(b)))
k=[3,0,-5,11,-2,7];s=[-1,0,8,1,-3,-2];v=[x+y for x,y in zip(k,s)]
need(corr(k,k)==corr(v,v)-2*corr(k,s)-corr(s,s),'sign of deletion')
print('Checked',n,'profiles/cuts, actual remaining odd signs, and signed reflection identity.')
