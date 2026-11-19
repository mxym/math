"""Exact finite identities/constant replay, not an exhaustive proof of the theorem."""
from fractions import Fraction
from itertools import combinations, product

def check(ok):
    if not ok:
        raise ArithmeticError("exact assertion failed")

def cubes(rows):
    # A bitset on the subset lattice, formed via direct submask enumeration.
    u=0
    for row in rows:
        s=row
        while True:
            u |= 1<<s
            if not s:break
            s=(s-1)&row
    return u

def direct_dom(A):
    n=len(A);allv=(1<<n)-1;ok=0
    # Compute actual dominated vertices by selected vertices (not by missed rows).
    covered=[0]*(1<<n)
    for s in range(1,1<<n):
        bit=s&-s
        covered[s]=covered[s^bit] | A[bit.bit_length()-1] | bit
        ok+=covered[s]==allv
    return ok

def rows(n,mask):
    A=[0]*n
    for k,(i,j) in enumerate(combinations(range(n),2)):
        if mask>>k&1:
            A[i]|=1<<j;A[j]|=1<<i
    return A
def comp(A):
    n=len(A);v=(1<<n)-1
    return [v^a^(1<<i) for i,a in enumerate(A)]

def finite():
    for n in range(2,7):
        best=None;ties=0;nb=0;pair_tests=0
        for mask in range(1<<(n*(n-1)//2)):
            A=rows(n,mask);B=comp(A)
            u=cubes(A);v=cubes(B);D=u.bit_count()+v.bit_count()
            check(D==(2<<n)-direct_dom(A)-direct_dom(B))
            for i,j in combinations(range(n),2):
                # Direction j vs i: the missing i coordinate is new in
                # one unlumped family and contributes at least half the j cube.
                if A[j]>>i&1:R,Q=A[j],A[i]
                else:R,Q=B[j],B[i]
                check(R>>i&1 and not Q>>i&1)
                check(2*((1<<R.bit_count())-(1<<(R&Q).bit_count()))>=1<<R.bit_count())
                check(abs((A[i]^A[j]).bit_count()-(B[i]^B[j]).bit_count())<=2)
                pair_tests+=1
            if best is None or D<best:best=D;ties=1
            elif D==best:ties+=1
            nb+=1
        check(best==2*((1<<(n//2))+(1<<(n-n//2)))-4)
        print(f'n={n} labelled_graphs={nb} min_deficit={best} ties={ties} pair tests={pair_tests}')

if __name__=='__main__':finite()
