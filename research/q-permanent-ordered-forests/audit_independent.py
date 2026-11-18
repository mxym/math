"""Exact cross-checks independent of verify.py. Python 3 + SymPy; -O supported."""
from itertools import permutations, combinations, product
from collections import Counter
from functools import cache
from math import comb, prod, factorial
from sympy import I, Matrix, eye, zeros, symbols, expand

def need(ok, label):
    if not ok: raise ArithmeticError(label)

def inversions(p):
    return sum(1 for a,b in combinations(p,2) if a>b)

def full_swap_poly(n, pairs):
    # One-line perms on actual coordinates; no crossing graph / token construction.
    h=Counter()
    for flags in product([False,True],repeat=len(pairs)):
        p=list(range(n))
        for (i,j),flag in zip(pairs,flags):
            if flag: p[i],p[j]=j,i
        h[inversions(p)]+=1
    return h

@cache
def confirm_layers(poly):
    # Bernstein coefficients of H(-r) at its native polynomial degree D,
    # scaled by D! to avoid fractions. Directly confirm they are decreasing.
    D=poly[-1][0]; scale=factorial(D)
    coeff=[sum(((-1)**m)*c*comb(k,m)*(scale//comb(D,m))
               for m,c in poly if m<=k) for k in range(D+1)]
    need(coeff[0]==scale and coeff[-1]==0 and all(b<=a for a,b in zip(coeff,coeff[1:])),
         ("Bernstein",poly,coeff))

def involutions(n):
    c=0
    for p in permutations(range(n)):
        if any(p[p[i]]!=i for i in range(n)): continue
        pairs=tuple((i,j) for i,j in enumerate(p) if j>i)
        if pairs:
            h=full_swap_poly(n,pairs)
            confirm_layers(tuple(sorted(h.items())))
            need(max(h)==inversions(p),"unexpected degree")
        c+=1
    return c

def gram_check(private):
    n=6
    # Color c is supported on the two ends of one tree edge, or a private vertex.
    endpoints=[(0,3),(1,4),(2,5),(1,3),(3,5)]
    cols=[]
    for k,(i,j) in enumerate(endpoints):
        col=zeros(n,1);col[i]=1+(k%3+1)*I;col[j]=k%2+1-I
        cols.append(col)
    if private: cols.extend(eye(n)[:,i] for i in range(n))
    V=Matrix.hstack(*cols); A=(V*V.H).applyfunc(expand)
    need(A.rank()==n-1+int(private),"Gram rank")
    # Compute exact support matching probabilities via choices of a color at each vertex.
    # These masses have common denominator prod_i A_ii, not included here.
    mass=Counter(); options=[list(j for j in range(V.cols) if V[i,j]) for i in range(n)]
    for marks in product(*options):
        pairs=tuple(e for ie,e in enumerate(endpoints) if all(marks[i]==ie for i in e))
        mass[pairs]+=prod(expand(V[i,j]*V[i,j].conjugate()) for i,j in enumerate(marks))
    need(sum(mass.values())==prod(A[i,i] for i in range(n)),"normalization")
    pol=Counter()
    for flags in product([False,True],repeat=len(endpoints)):
        F=tuple(e for e,flag in zip(endpoints,flags) if flag); cover={v for e in F for v in e}
        if len(cover)!=2*len(F): continue
        rem=sorted(set(range(n))-cover)
        b=prod(expand(A[i,j]*A[j,i]) for i,j in F)*A.extract(rem,rem).det(method="bareiss")
        need(expand(b-mass[F])==0,("color masses vs. determinant",F))
        for degree,count in full_swap_poly(n,F).items(): pol[degree]+=mass[F]*count
    direct=Counter()
    for p in permutations(range(n)):
        v=prod(A[i,j] for i,j in enumerate(p))
        if v!=0: direct[inversions(p)]+=expand(v)
    need(all(expand(pol[k]-direct[k])==0 for k in pol.keys()|direct.keys()),"direct q-permanent")
    return len(mass)
def block_example():
    t,q=symbols("t q",real=True)
    B=Matrix([[1,t],[t,1]]); A=Matrix.diag(B,B)
    p=sum(q**inversions(v)*prod(A[i,j] for i,j in enumerate(v)) for v in permutations(range(4)))
    need(expand(p-(1+t*t*q)**2)==0,"left sharpness")
if __name__=="__main__":
    print("Involutions tested directly on 9 points:",involutions(9))
    print("Distinct nonconstant polynomials, exact decreasing Bernstein layers:",confirm_layers.cache_info().currsize)
    print("Positive masses in singular / positive-definite complex tree:",gram_check(False),gram_check(True))
    block_example()
    print("No uniform left extension: exact two-block formula checked.")
