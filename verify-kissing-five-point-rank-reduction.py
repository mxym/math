#!/usr/bin/env python3
"""Finite exact controls for the five-point global rank reduction."""
from itertools import combinations,product
from fractions import Fraction as F
from collections import Counter
n=5;P=list(combinations(range(n),2));T=list(combinations(range(n),3))
def edge(a,b):return tuple(sorted((a,b)))
def main():
    labelled=0;cases=0;matches=Counter()
    for mask in range(1<<len(P)):
        E={e for k,e in enumerate(P)if mask>>k&1}
        if any(len(set(combinations(t,2))&E)in(0,3)for t in T):continue
        labelled+=1;N=[{j for j in range(n)if i!=j and edge(i,j)in E}for i in range(n)]
        assert all(len(v)==2 for v in N)
        seq=[0,min(N[0])]
        for i in range(3):seq.append(next(iter(N[seq[-1]]-{seq[-2]})))
        assert len(set(seq))==5 and edge(seq[-1],seq[0])in E
        chords=[edge(seq[i],seq[(i+2)%5]) for i in range(5)]
        for cm in range(32):
            contacts=[p for i,p in enumerate(chords) if cm>>i&1]
            if any(set(a)&set(b) for a,b in combinations(contacts,2)):continue
            assert len(contacts)<=2
            matches[len(contacts)]+=1;cases+=1
            i=next(i for i in range(5) if not cm>>i&1 and not cm>>((i+1)%5)&1)
            L=Counter(chords[i]+chords[(i+1)%5])
            R=Counter([seq[(i+k)%5] for k in range(4)])
            assert L==R
            assert edge(seq[i],seq[(i+1)%5])in E and edge(seq[(i+2)%5],seq[(i+3)%5])in E
    assert (labelled,cases,matches)==(12,132,Counter({0:12,1:60,2:60}))
    # The two interior critical values of -f' have squared value 1/216.
    assert F(1,216)<F(1,16)
    for d in range(1,6):
        S=[[F((1+i+j)**2-2*i*j,9)for j in range(d)]for i in range(d)]
        tr=sum(S[i][i]for i in range(d))
        for i,j in product(range(d),repeat=2):
            def entry(a):
                return sum((a[k]==a[l])*S[a[m]][a[nn]] for k,l in combinations(range(4),2)
                           for m,nn in [tuple(z for z in range(4)if z not in(k,l))])/6
            x=sum(entry([i,j,k,k])for k in range(d))
            assert x==((d+4)*S[i][j]+(i==j)*tr)/6
        assert F(d+2,3)<=F(7,3)<4
    print('PASS:',labelled,'labelled strong cycles;',cases,'admissible labelled contact choices; d=1..5 traces')
if __name__=='__main__':main()
