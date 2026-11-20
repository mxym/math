from itertools import combinations,product
from collections import Counter
def core(ids,es):
 a=[0]*ids
 for i,j in es:a[i]|=1<<j;a[j]|=1<<i
 return a
fixed=[(0,i) for i in (3,4,5)]+[(1,i) for i in (6,7,8)]+[(2,i) for i in (3,4,6,7)]+[(3,5),(6,8)]
# N=0,1; T=2, A=3,4,5 with 3,4~T; B=6,7,8 with 6,7~T
c=0
for f in combinations(product([3,4,5],[6,7,8]),5):
 a=core(9,fixed+list(f))
 if [x.bit_count()for x in a] != [3,3,4,4,4,4,4,4,4]:continue
 if any((a[i]&a[j]).bit_count()+(a[i]>>j&1)>2 for i,j in combinations(range(9),2)):continue
 print(f,a);c+=1
print(c)
