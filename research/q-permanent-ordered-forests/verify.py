"""Exact finite illustrations only, Python stdlib; safe to run with -O."""
from collections import Counter
from itertools import combinations, permutations
from math import prod

def check(p, msg):
    if not p: raise ArithmeticError(msg)
def subsets(t):
    return (u for n in range(len(t)+1) for u in combinations(t,n))
def matchings(verts):
    if not verts:
        yield (); return
    a,*tail=verts
    yield from matchings(tail)
    for i,b in enumerate(tail):
        for rem in matchings(tail[:i]+tail[i+1:]): yield ((a,b),)+rem
def le(e): return 2*(e[1]-e[0])-1
def cross(e,f):
    a,b=e;c,d=f
    return a<c<b<d or c<a<d<b
def inv(p): return sum(a>b for i,a in enumerate(p) for b in p[i+1:])
def invmatching(s,n):
    p=list(range(n))
    for a,b in s:p[a],p[b]=p[b],p[a]
    return inv(p)
def tok(f):
    sets={e:set() for e in f}
    for e,g in combinations(f,2):
        if cross(e,g):
            for h in (0,1):
                sets[e].add((e,g,h));sets[g].add((e,g,h))
    for e in f:
        n=le(e)-len(sets[e]);check(n>=1,('private tokens',f,e))
        sets[e].update((e,j) for j in range(n))
    return sets
def at_minus_one_deriv(poly): return sum(k*v*(-1)**(k-1) for k,v in poly.items() if k)
def run_combinatorics(n):
    count=0
    for f in matchings(list(range(n))):
        sets=tok(f);h=Counter()
        for s in subsets(f):
            ell=invmatching(s,n);h[ell]+=1;count+=1
            check(ell==len(set().union(*(sets[e] for e in s))),('union',s))
            check((ell-len(s))%2==0,('parity',s))
        D=0 if not f else len(set.intersection(*(sets[e] for e in f)))
        check(at_minus_one_deriv(h)==D,('endpoint derivative',f))
    return count
def matrix_poly(A, rows):
    result=Counter()
    for perm in permutations(rows):
        h=prod(A[i][j] for i,j in zip(rows,perm))
        if h: result[inv(perm)]+=h
    return result
def det(A,ii):
    return sum(c*(-1)**k for k,c in matrix_poly(A,ii).items())
def matrix_test(A):
    n=len(A); rows=list(range(n));p=matrix_poly(A,rows);exp=Counter();crossdiff=0
    for f in matchings(rows):
        h=prod(A[i][j]*A[j][i] for i,j in f)
        if not h:continue
        consumed={v for e in f for v in e};b=h*det(A,[v for v in rows if v not in consumed])
        check(b>=0,'positive minor')
        if len(f)==1:crossdiff+=le(f[0])*b
        if len(f)==2 and cross(*f):crossdiff+=2*b
        for s in subsets(f):exp[invmatching(s,n)]+=b
    check(p==exp,'coefficientwise identity')
    check(at_minus_one_deriv(p)==crossdiff,'exact forest derivative')
    return sorted((k,v) for k,v in p.items() if v)
if __name__=='__main__':
    print('Exact matching/submatching inversion tests on eight positions:',run_combinatorics(8))
    # Integer strictly diagonally dominant tree, with multiple crossings.
    n=7;A=[[0]*n for _ in range(n)]
    for i,j,w in [(0,3,2),(1,4,-1),(2,5,3),(3,4,-2),(4,5,1),(5,6,2)]:
        A[i][j]=A[j][i]=w
    for i in range(n): A[i][i]=1+sum(abs(v) for v in A[i])
    print('Crossing connected weighted tree coefficients:',matrix_test(A))
    B=[[int(i==j or abs(i-j)==2) for j in range(4)] for i in range(4)]
    check(matrix_test(B)==[(0,1),(3,2),(4,1)],'embedded rank two')
    print('Singular, crossing two-edge boundary example passed.')
