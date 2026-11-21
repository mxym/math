"""Integer, cutoff-free algebra comparison. Does not depend on Python assertions."""
from functools import cache
from itertools import product
from collections import Counter
from math import prod

def need(test, label):
    if not test:
        raise ValueError(label)

@cache
def partitions(total, k, start=1):
    if k == 1:
        return ((total,),) if total >= start else ()
    return tuple((x,) + p for x in range(start, total // k + 1)
                 for p in partitions(total-x, k-1, x))

@cache
def divs(x):
    out = [(0,1)]
    for a in x:
        out += [(b+a,-m) for b,m in out]
    return tuple(out)

def m0(x):
    return sum(m for b,m in divs(x) if 2*b < sum(x))

def kernel0(x,y):
    norm = sum(x)+sum(y)
    return sum(m*max(0,norm-2*d)**2 for d,m in divs(x+y))

def raw_pre(x,y):
    def t2(a):
        return 8*prod(a) if len(a)==2 else 0
    return kernel0(x,y)-t2(x)*m0(y)-t2(y)*m0(x)

def sourced(x,y):
    if len(x)!=3:
        return 0
    N = sum(x)
    return 8*sum(m*(sum(e*max(0,d-b)**2 for b,e in divs(x))
                  +m0(x)*d*(N-d)) for d,m in divs(y) if 2*d < N)

def check():
    counts = Counter()
    for total in (11,13,15):
        rows = {k:partitions(total,k) for k in range(1,9)}
        for x in rows[3]:
            need(m0(x)==(-2 if 2*max(x)<total else 0), ("balance",x))
            need(2*sum(d*m for d,m in divs(x) if 2*d<total)==total*m0(x),
                 ("first moment",x))
        for a,b in ((3,2),(3,4),(3,6),(3,8),(3,3),(1,3),
                    (2,2),(2,4),(2,6),(4,4),(4,6)):
            for x,y in product(rows[a],rows[b]):
                value = raw_pre(x,y)-sourced(x,y)-sourced(y,x)
                expected = -4*total**2*m0(x)*m0(y) if a==b==3 else 0
                need(value==expected, (x,y,value,expected))
                if expected < 0:
                    counts["strictly negative triples"]+=1
                if (a,b)==(3,2) and raw_pre(x,y)>0:
                    counts["initial genuinely positive 3x2"]+=1
                counts["comparisons"]+=1
    need(counts["initial genuinely positive 3x2"]>0 and
         counts["strictly negative triples"]>0,"inactive controls")
    print(dict(counts))

if __name__=="__main__":
    check()
