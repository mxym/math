from itertools import combinations
from math import gcd,prod
from functools import reduce
base={3,5,7,11,13,19,23,47};opt={17,31,37}
def req(v):
 if not v:raise ArithmeticError()
n=0
for k in range(4):
 for S in combinations(sorted(opt),k):
  P=sorted(base|set(S))
  for p in P:
   h=2*p+1;u=h;w=abs(25-h);D=[]
   req(w!=0)
   for q in [2]+P:
    a=0
    while u%q==0:u//=q;a+=1
    if q>2:D.append(2*(q==5)-a)
    if q==2 or q in base:
     while w%q==0:w//=q
   req(u==w==1 and reduce(gcd,(abs(a-b) for a,b in combinations(D,2)),0)==1)
   n+=1
print('all 8 alphabets; checked',n,'support/difference/primitive-valuation rows')
