"""Small exact checks of the two elementary reductions; not a rerun of Pantone--Vatter."""
from itertools import permutations,product
from fractions import Fraction
from math import comb
from collections import Counter

def chk(test,detail):
    if not test: raise RuntimeError(str(detail))
def desc(w):
    return sum(x>y for x,y in zip(w,w[1:]))
def inv(w):
    return sum(x>y for i,x in enumerate(w) for y in w[i+1:])
def indecomp_lengths(w):
    lo=0; hi=-1; sizes=[]
    for i,v in enumerate(w):
        hi=max(hi,v)
        if hi==i:sizes.append(i+1-lo);lo=i+1
    return sizes
def main():
    w=4106;b=36953
    chk(8*(w+513)==b-1 and 9*w==b+1,'source constants')
    fiber_tests=0;profile_checks=0;heredity=0
    for n in range(1,9):
        perms=list(permutations(range(n)))
        for k in range(1,5):
            seen=Counter(tuple(sorted(range(n),key=lambda i:(f[i],i))) for f in product(range(k),repeat=n))
            testset={p for p in perms if desc(p)<k}
            chk(set(seen)==testset,(n,k,'support'))
            for p,v in seen.items():
                d=desc(p)
                chk(v==comb(n+k-1-d,k-1-d),(n,k,p,'fiber'))
                fiber_tests+=1
        for p in perms:
            s=indecomp_lengths(p); v=inv(p)
            if n>1:
                q=tuple(n-1-x for x in p)
                chk(v+inv(q)==comb(n,2),(p,'reflection'))
                # Count ordered choices of two points with opposite orders:
                # distinct cells 2*v, same cell inversion probability 1/2.
                f=Fraction(4*v+n,2*n*n)
                chk(f==(1-Fraction(1,n))*Fraction(v,comb(n,2))+Fraction(1,2*n),p)
                chk((f>=Fraction(1,2))==(2*v>=comb(n,2)),(p,f))
            chk(sum(s)==n and all(abs(i-x)<max(s) for i,x in enumerate(p)),(p,s))
            chk(v<=sum(comb(j,2) for j in s),(p,s,'block bound'))
            profile_checks+=1
            for i in range(n):
                q=tuple(x-(x>p[i]) for j,x in enumerate(p) if j!=i)
                chk(desc(q)<=desc(p) and max(indecomp_lengths(q),default=0)<=max(s),(p,q))
                heredity+=1
    print('PV input constants: w=4106, 36952 < 36953 < 36954.')
    print('Bounded-descent color-map exact fiber counts:',fiber_tests)
    print('Literal permutations checking empirical inversion, reflection and blocks through n=8:',profile_checks)
    print('Single-position hereditary deletion tests:',heredity)
    print('PASS (finite sanity checks; asymptotic proof is analytic using the cited theorem).')
if __name__=='__main__': main()
