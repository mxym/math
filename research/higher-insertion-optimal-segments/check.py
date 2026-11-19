from collections import Counter
from itertools import combinations
from math import comb,prod
def hh(y,k):
 c=Counter(''.join(a for i,a in enumerate(y) if i not in mask) for mask in combinations(range(len(y)), k))
 if sum(c.values())!=comb(len(y),k):raise ValueError('mass')
 return Counter(c.values())
def val(h):return prod(t**(t*m) for t,m in h.items())
a=hh('01'*9,4);d=hh('010101010010101010',4)
if a!={1:1365,15:105,120:1} or d!={1:850,2:230,7:20,8:84,9:30,15:12,22:2,28:10,43:2,78:1} or not val(d)<val(a):raise ArithmeticError
print('n=18, k=4: checked both exact histograms and strict entropy advantage for centered double.')
