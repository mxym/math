"""Cross-check a bounded subset of exact finite-difference signs."""
def comps(n,k,lo=1):
 if k==1:
  if n>=lo:yield (n,)
  return
 for i in range(lo,n//k+1):
  for z in comps(n-i,k-1,i):yield (i,)+z
def num(t,R):
 n=sum(t);terms=[(0,1)]
 for u in t:terms += [(v+u,-s) for v,s in terms]
 return sum(s*max(0,n-2*v)**R for v,s in terms)
count=0
for R in [2,3,4,5,6,7,8]:
 for k in range(2,R+1):
  for t in comps(33,k):
   if num(t,R)<0: raise ValueError((R,t))
   count+=1
print(count,'bounded profiles have the proven sign.')
