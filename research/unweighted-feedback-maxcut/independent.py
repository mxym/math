"""Independent grouped-binomial recomputation; explicit failure checks survive Python -O."""
from math import comb, prod
from collections import Counter
from itertools import product
def require(condition, description):
    if not condition: raise ArithmeticError(description)

ties, mins, cells = [], [], 0
for n in range(2, 17):
    row=[]
    for m in range(n-1, 1+comb(n,2)):
        if n==2: x={1:2}
        else:
            q,r=divmod(2*m-n,n-2)
            x=Counter([n-1]*q+[1+r]*bool(r)+[1]*(n-q-bool(r)))
        require(sum(k*v for k,v in x.items())==2*m and sum(x.values())==n,(n,m,x))
        A=0
        for term in product(*(list((w*(2*j-k),comb(k,j)) for j in range(k+1)) for w,k in x.items())):
            A += abs(sum(y for y,c in term))*prod(c for y,c in term)
        c_bound, rem = divmod(2*m+n-1,4)
        g=15*(c_bound+bool(rem))*2**n-6*m*2**n-4*A
        require(g>=0,(n,m,g))
        cells+=1
        if not g:ties.append((n,m))
        row.append(g)
    mins.append(min(row))
require(cells==575 and ties==[(3,3),(5,10)],(cells,ties))
require(mins==[20,0,96,0,288,192,1856,1536,7680,11264,43008,49152,172032,294912,884736],mins)
print(mins, ties)
