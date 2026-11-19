"""Exact alternate finite certificate with character-slice mask outputs."""
from collections import Counter
from itertools import combinations, repeat
from math import prod

def require(value, data):
    if not value:
        raise ArithmeticError(data)

def materialize(L):
    acc=''
    for length in L:
        first=acc[-1:] or '0'
        second='1' if first=='0' else '0'
        acc+=((first+second)*((length+1)//2))[:length]
    return acc

def exact(L):
    w=materialize(L)
    n=len(w)
    C=Counter(w[:i]+w[i+1:j]+w[j+1:k]+w[k+1:]
              for i,j,k in combinations(range(n),3))
    return prod(z**z for z in C.values())

def finite():
    run_only=balanced=coarse=direct=end=0; largest_residual=0
    for n in range(7,130):
        m=n-2; target=m**(m*m)
        if m<16:
            for l in (1,2):
                require(exact((l,n-l))>target,('endpoint',n,l))
                end+=1
        g=[0]+[(max(1,l-1)**((l-1)*(n-l))) *
               (max(1,l-2)**(max(0,l-2)**2)) for l in range(1,n+1)]
        require(all(g[l]*g[l]<=g[l-1]*g[l+1] for l in range(2,n)),('convex',n))
        for D in range(2,n):
            r=1<<(D*m*(m-1))
            if r>target:
                run_only+=1;continue
            q,s=divmod(n,D+1)
            factors=list(repeat(g[q],D+1-s))
            if s:factors.extend(repeat(g[q+1],s))
            if r*prod(factors)>target:
                balanced+=1;continue
            for bars in combinations(range(1,n),D):
                b=(0,)+bars+(n,)
                L=tuple(b[i+1]-b[i] for i in range(len(b)-1))
                if r*prod(g[l] for l in L)>target:
                    coarse+=1
                else:
                    require(exact(L)>target,('direct',n,L))
                    direct+=1
                    largest_residual=max(largest_residual,n)
    print(f"PASS n=7..129 | run-only={run_only} | balanced={balanced} | coarse={coarse} | exact={direct} (largest n={largest_residual}) | boundary={end}")
if __name__=="__main__":
    finite()
