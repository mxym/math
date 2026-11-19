#!/usr/bin/env python3
"""Exact finite checks for flagged qubit POVMs. Standard library; no solver."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from functools import reduce
from operator import or_

I = (F(1), F(0), F(1))  # coordinates of a real symmetric two-by-two matrix
Z = (F(0), F(0), F(0))
def require(condition, message):
    if not condition:
        raise ArithmeticError(message)
def add(A,B): return tuple(a+b for a,b in zip(A,B))
def sc(t,A): return tuple(t*a for a in A)
def sub(A,B): return add(A,sc(-1,B))
def psd(A):
    a,b,c=A
    return a>=0 and c>=0 and a*c>=b*b
def ray(a,b):
    return tuple(F(h,a*a+b*b) for h in (a*a,a*b,b*b))
def contained(s,t): return (s&t)==s
def facets_of(k):
    return tuple(s for s in k if not any(s!=t and contained(s,t) for t in k))
def all_complexes(n):
    # Enumerate every face list with all vertices; reject if downward closure fails.
    mandatory={0}|{1<<i for i in range(n)}
    optional=sorted(set(range(1<<n))-mandatory)
    for bits in range(1<<len(optional)):
        k=mandatory | {s for j,s in enumerate(optional) if (bits>>j)&1}
        if all(s^(1<<i) in k for s in k for i in range(n) if s&(1<<i)):
            yield facets_of(k)
def count(n,facets,full_tuples,stats):
    m=len(facets); w=F(2,2*m-1); e=F(1,2*n*(2*m-1))
    dim=m+n
    P={}
    for j in range(dim):
        k=j+1; den=dim+1
        P[j,0]=ray(den,k); P[j,1]=ray(-k,den)
        require(add(P[j,0],P[j,1])==I,'basis does not sum to the identity')
    require(len(set(P.values()))==2*dim, 'repeated normalized real ray')
    E={}; named=[]
    for i in range(n):
        E[i]={label:sc(w if label[0]<m else e,Q) for label,Q in P.items()
              if (label[0]<m and not facets[label[0]]&(1<<i)) or label[0]==m+i}
        E[i][None]=sub(I,reduce(add,E[i].values(),Z))
        named.append(tuple(E[i]))
        require(all(psd(A) and A!=Z for A in E[i].values()), 'invalid effect')
        require(len(E[i])<=2*m+1, 'outcome bound')
    for mask in range(1<<n):
        S=[i for i in range(n) if mask&(1<<i)]
        isface=any(contained(mask,f) for f in facets)
        if isface:
            proto={j for i in S for j in named[i]}-{None}
            parent=defaultdict(lambda:Z)
            raw={}
            for label in proto:
                Q=sc(w if label[0]<m else e,P[label]);raw[label]=Q
                x=tuple(label if label in E[i] else None for i in S)
                parent[x]=add(parent[x],Q)
            x=(None,)*len(S)
            parent[x]=add(parent[x],sub(I,reduce(add,raw.values(),Z)))
            require(all(psd(Q) for Q in parent.values()),'nonpositive parent')
            require(reduce(add,parent.values(),Z)==I,'parent normalization')
            for k,i in enumerate(S):
                for label,expected in E[i].items():
                    actual=reduce(add,(Q for x,Q in parent.items() if x[k]==label),Z)
                    require(actual==expected,'incorrect marginal')
            stats['face_parents']+=1
        else:
            representative={j:next(i for i in S if (j,0) in E[i]) for j in range(m)}
            selected=reduce(add,(E[i][j,b] for j,i in representative.items() for b in (0,1)),Z)
            require(selected==sc(m*w,I) and not psd(sub(I,selected)),'no weight obstruction')
            if full_tuples:
                # Positive tuple effect counted at least twice would require two distinct
                # supports. Test that fact on every tuple in every <=4-vertex nonface.
                named_to_P=[{a:P[a] for a in E[i] if a is not None and a[0]<m and
                           representative[a[0]]==i} for i in S]
                for x in product(*(named[i] for i in S)):
                    rays=[tab[a] for a,tab in zip(x,named_to_P) if a in tab]
                    require(len(rays)==len(set(rays)),'unjustified event collision')
                    stats['nonface_tuples']+=1
            stats['nonface_witnesses']+=1
    stats['complexes']+=1
def main():
    stats=Counter()
    for n in range(1,5):
        c=0
        for fac in all_complexes(n):
            count(n,fac,True,stats); c+=1
        print(f'n={n}: {c} labelled complexes (all)')
    for n,fac in [(7,[(1<<i)|1 for i in range(1,7)]),
                  (6,[(1<<i)|(1<<j) for i,j in combinations(range(6),2)]),
                  (7,[(1<<7)-1-(1<<i) for i in range(7)])]:
        count(n,fac,False,stats)
    print('Also checked: seven-vertex star, six-vertex edge-only complete structure, seven-Specker scenario.')
    print(dict(sorted(stats.items())));print('PASS')
if __name__=='__main__':main()
