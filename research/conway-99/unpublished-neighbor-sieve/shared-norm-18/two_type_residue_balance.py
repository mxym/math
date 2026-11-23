"""Fixed-H projective-shell equalities in the (18,24)-only unit face.
Python 3.8+, standard library. No graph symmetry assumed.
"""
from itertools import product, combinations_with_replacement
from collections import Counter
from fractions import Fraction

B = ((2,1,0,0),(1,4,0,0),(0,0,2,1),(0,0,1,4))
D = ((4,-1,0,0),(-1,2,0,0),(0,0,4,-1),(0,0,-1,2)) # 7 B^{-1}
shifts = (None,(-2,0,0,0),(-2,1,0,0),(-1,1,-1,1))
pairs = list(combinations_with_replacement(range(4),2))
zero = (0,0,(0,0))

def dot(x,y): return sum(u*v for u,v in zip(x,y))
def times(b,x): return tuple(dot(row,x) for row in b)
def anti(x): return min(tuple(x),tuple((-z)%7 for z in x))

def pts(sh):
    den = 1 if sh is None else 3
    if sh is None: cos = [((0,0,0,0),1)]
    else: cos = [(tuple(j*x%3 for x in times(B,sh)),3) for j in (-1,0,1)]
    for offs,step in cos:
        # conservative bounds from (h,e_i)^2 <= 4 B_ii
        m = 4*den
        for g in product(*[range(-m+(m+o)%step,m+1,step) for o in offs]):
            h = dot(g,times(D,g))
            q = 28*den**2-h
            if q < 0: continue
            for a in ((0,3) if sh is None else (((-dot(sh,g)+4)%9-4),)):
                if a < 0: continue
                n,r = divmod(9*q+11*a*a*den**2,9*den**2)
                if r or n<11*a or (n-11*a)%2 or (a==0 and 0<n<14) or (a==1 and n<=19) or (a,n)==(2,24): continue
                # Implied FULL shell vanishings, not a general unit/full identification.
                if (a,n) in ((0,16),(0,20),(0,26),(1,21),(1,25),(2,26),(2,28),(2,30),(3,37)): continue
                c=tuple((g[i]+5*g[i+1])*pow(den,-1,7)%7 for i in (0,2))
                yield a,n,g,c,(2 if a else 1)

def row(o,sh,ij,points):
    i,j=ij; res=Counter(); den=1 if sh is None else 3
    def harm(g):return 2*g[i]*g[j]-B[i][j]*g[0]**2
    for a,n,g,c,m in points:
        v=anti(tuple(dot(r,c)%7 for r in o))
        if (a,n)==(1,27): a,n,m=0,18,9*m
        res[a,n,v]+=m*harm(g)
    for k in (0,2):
        if sh is None or dot(B[k],sh)%3==0:
            res[zero]+=2*48*harm([den*x for x in B[k]])
    return res

# Entries (matrix first column/remaining explicitly, shift index, harmonic ij, integer multiplier).
cert = [
 (((0,1),(6,0)),1,(1,3),4),
 (((0,1),(6,0)),3,(0,2),3), (((0,1),(6,0)),3,(0,3),5), (((0,1),(6,0)),3,(1,2),1),
 (((0,1),(1,0)),3,(0,2),-3), (((0,1),(1,0)),3,(0,3),-5), (((0,1),(1,0)),3,(1,2),-1),
 (((1,0),(0,6)),1,(1,3),2),
 (((2,2),(5,2)),1,(1,1),-3), (((2,2),(5,2)),3,(2,2),3),
 (((2,2),(2,5)),1,(1,1),3), (((2,5),(2,2)),3,(1,1),-3),
 (((2,5),(5,5)),3,(1,1),3)
]
def main():
    allpts={s:list(pts(s)) for s in shifts}
    group=[((i,j),((-t*j)%7,(t*i)%7)) for i,j in product(range(7),repeat=2) if (i*i+j*j)%7==1 for t in (1,-1)]
    assert len(set(group))==16
    z=Counter()
    for o,s,j,f in cert:
        assert o in group
        for k,v in row(o,shifts[s],j,allpts[shifts[s]]).items():z[k]+=f*v
    assert {k:v for k,v in z.items() if v}=={(0,18,(2,3)):1728,(0,18,(2,4)):-1728}
    r=((2,5),(2,2));v=(2,3);vs=[]
    for _ in range(4):
        vs.append(anti(v));v=tuple(x%7 for x in times(r,v))
    assert len(set(vs))==4 and vs[1]==(2,4)
    print("13-row identity: 1728 times the adjacent norm-18 projective-class difference; rotation orbit",vs)
    # Independently verify the other equality assertions by sparse exact elimination.
    basis={}
    def reduce(x,add=False):
        while x:
            i=min(x);v=x[i]
            if i not in basis:
                if add:basis[i]={j:Fraction(w,v) for j,w in x.items()}
                return False
            for j,w in basis[i].items():
                z=x.get(j,0)-v*w
                if z:x[j]=z
                else:x.pop(j,None)
        return True
    sets={}
    for o in group:
        for sh in shifts:
            for j in pairs:
                rr=row(o,sh,j,allpts[sh])
                for a,n,v in rr:sets.setdefault((a,n),set()).add(v)
                reduce({k:h for k,h in rr.items() if h},True)
    assert len(basis)==30
    equal=[]
    for at,vs in sorted(sets.items()):
        if len(vs)!=4:continue
        f=min(vs)
        if all(reduce({(*at,f):1,(*at,v):-1}) for v in vs if v!=f):equal.append(at)
    assert equal==[(0,18),(0,24),(1,29),(2,32),(3,35),(4,44)]
    print("rank",len(basis),"; all four equal on",equal)
def check_matching_cap():
    from itertools import combinations_with_replacement
    def dim(n):
        return 0 if not n else (24*(n-1)+n+23)//(n+24)
    best = max(sum(v) for v in combinations_with_replacement(range(51), 4)
               if sum(map(dim, v)) + 2*(sum(n>0 for n in v)>=3) <= 43)
    assert best == 117
    assert (200-best+1)//2 == 42
    print("Edgeless class-size cap 117; at least 42 disjoint overlapping pairs.")

if __name__=='__main__':
    main()
    check_matching_cap()
