from itertools import product
from collections import Counter
from math import comb
def require(condition, explanation):
    if not condition: raise ArithmeticError(explanation)
def words(q,n):
    return product(range(q),repeat=n)
def embedding(x,y):
    a=[1]+[0]*len(y)
    for c in x:
        for i in range(len(y)-1,-1,-1):
            if y[i]==c: a[i+1]+=a[i]
    return a[-1]
def row(q,m,d,y):
    return sorted((embedding(x,y) for x in words(q,m+d)),reverse=True)
def partitions(y,d):
    return {(i,j) for i in range(len(y)) for j in range(i+1,min(len(y),i+d+1)) if y[i]==y[j]}
cases=0
for m,d in ((1,1),(4,2),(4,3),(5,3),(4,4),(6,2)):
    rs=[]
    for y in words(2,m):
        r=row(2,m,d,y)
        rr=1+sum(y[i]!=y[i-1] for i in range(1,m))
        require(sum(v>0 for v in r)==sum(comb(m+d,h) for h in range(d+1)), 'sum(v>0 for v in r)==sum(comb(m+d,h) for h in range(d+1))')
        require(r.count(1)==comb(d+m-rr+1,d), 'r.count(1)==comb(d+m-rr+1,d)')
        rs.append(r)
    if d==2:
        want=min(max(4,m+1),max(6,3+(m-1)//2),9)
        require(min(r[0] for r in rs)==want, 'min(r[0] for r in rs)==want')
    cases+=len(rs)
print('PASS independent DP fixed support, singleton and peak checks:',cases)
cases=0
for q,m,d in ((2,4,2),(3,3,2),(3,4,2),(4,3,3)):
    ws=list(words(q,m))
    rows={y: row(q,m,d,y) for y in ws}
    for y in ws:
        for z in ws:
            ey,ez=partitions(y,d),partitions(z,d)
            if not ez<=ey: continue
            p=0
            for a,b in zip(rows[y],rows[z]):
                p+=a-b
                require(p>=0, 'p>=0')
            require(p==0, 'p==0')
            require((rows[y]==rows[z]) == (ey==ez), '(rows[y]==rows[z]) == (ey==ez)')
            cases+=1
print('PASS independent DP local collision comparisons:',cases)
