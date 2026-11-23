"""Universal rooted dyadic scalar lattice and its short primal shells. Python 3."""
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, combinations, product
from math import factorial, prod

pairs = [(i,j) for i,j in combinations(range(14),2) if i//2!=j//2]

# Exact rank of the three 2-adic pivot subquotients via invertible row/column steps.
def pivot_counts(A):
    Z=[[z%8 for z in r] for r in A]; at=0; out=[]
    for level in (8,4,2):
        while True:
            p=next(((i,j) for i in range(at,len(Z))
                    for j in range(at,len(Z[0])) if Z[i][j]%2),None)
            if p is None: break
            i,j=p; Z[at],Z[i]=Z[i],Z[at]
            for row in Z: row[at],row[j]=row[j],row[at]
            f=pow(Z[at][at],-1,level)
            Z[at]=[f*x%level for x in Z[at]]
            for i in range(at+1,len(Z)):
                f=Z[i][at]; Z[i]=[(x-f*y)%level for x,y in zip(Z[i],Z[at])]
            at+=1
        out.append(at)
        for i in range(at,len(Z)):
            for j in range(at,len(Z[0])):
                assert Z[i][j]%2==0
                Z[i][j]//=2
    return out

def shapes():
    seen=set()
    for L in range(8):
        possible={}
        for a,b in product(range(16),repeat=2):
            kat=tuple(sorted(((L-3*a-b)%8,(L-3*b-a)%8)))
            possible.setdefault(kat,set()).add((a+b)%16)
        for v in combinations_with_replacement(sorted(possible),7):
            sums={0}
            for kat in v: sums={(x+y)%16 for x in sums for y in possible[kat]}
            if 2*L%16 not in sums: continue
            f=min(images(v))
            if f not in seen: yield f; seen.add(f)
def images(v):
    return {tuple(sorted(tuple(sorted(((sgn*a+h)%8,(sgn*b+h)%8))) for a,b in v))
            for sgn in (-1,1) for h in (0,4)}
def size(v):
    return factorial(7)*2**sum(a!=b for a,b in v)//prod(factorial(x) for x in Counter(v).values())
def data(v):
    a=sum((tuple(x) for x in v),())
    return [(a[i]+a[j])%8 for i,j in pairs]
@lru_cache(None)
def rowcost(q):
    x=[i if i<4 else i-8 for i in q]; assert sum(x)%8==0
    while sum(x):
        dx=8 if sum(x)<0 else -8
        i=min(range(len(x)), key=lambda i:(x[i]+dx)**2-x[i]**2)
        x[i]+=dx
    return sum(t*t for t in x)
def lower(v):
    q=data(v)
    return sum(rowcost(tuple(sorted(q[j] for j,p in enumerate(pairs) if i in p)))
               for i in range(14))//2
def dual(v,a):
    # sum (a_i+a_j)y_ij=0 by the fourteen zero row sums. All a are between -6 and 6,
    # so the nearest representative to (a_i+a_j)/2 lies in [-12,12].
    return sum(min(x*x-(a[i]+a[j])*x for x in range(-16,17) if (x-q)%8==0)
               for (i,j),q in zip(pairs,data(v)))
def main():
    K=[[2-3*len(set(p)&set(s))-len({i^1 for i in p}&set(s)) for s in pairs] for p in pairs]
    assert pivot_counts(K)==[6,7,8]
    V=list(shapes()); assert len(V)==230
    assert sum(size(w) for v in V for w in images(v))//2==2**21
    z=(0,0)
    lows={v:lower(v) for v in V if lower(v)<=336}
    assert lows=={(z,)*7:0, (z,)*6+((2,6),):192,
                  (z,)*5+((1,3),(5,7)):320, (z,)*5+((2,6),)*2:320,
                  ((0,2),)*4+((7,7),)*3:336, ((1,5),)*7:336}
    for v,a,t in [((z,)*6+((2,6),),[0]*12+[-4,4],288),
                  ((z,)*5+((1,3),(5,7)),[0]*10+[-6,-2,2,6],432),
                  ((z,)*5+((2,6),)*2,[0]*10+[-4,4,-4,4],448)]:
        assert dual(v,a)==t
    print('Dyadic valuations [0^6,1,2,3^22]; 230 shapes cover 2^21 residues.')
    print('Unconditional F1=F2=0; only the Fano or checkerboard F3 families remain.')
if __name__=='__main__': main()
