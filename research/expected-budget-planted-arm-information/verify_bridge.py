#!/usr/bin/env python3
"""Exact pairwise conditional-Hellinger bridge and tournament checks (not a proof by testing)."""
from fractions import Fraction as F
from itertools import product
from math import ceil

def ck(x,why):
    if not x: raise ArithmeticError(why)

def one(n,m,mode,U,V):
    # Components are integer square roots of single-observation masses times sqrt(D).
    D=sum(x*x for x in U); ck(sum(x*x for x in V)==D,'normalization')
    h2=F(sum((x-y)**2 for x,y in zip(U,V)),D)
    labels=list(range(n))
    family=[{i} for i in labels]+[{i,j} for i in labels for j in labels if i<j]
    leaves=0; lengths={i:0 for i in labels}; counts={(i,j):0 for i in labels for j in labels}
    dist={};mass=[0]*len(family)
    def visit(path,sq,N):
        nonlocal leaves
        k=len(path)
        if k==m or (mode and k>=2 and path[-2:]==(1,1)):
            leaves+=1; scale=D**(m-k)
            for u,s in enumerate(sq):
                mass[u]+=scale*s*s
                if u<n:
                    lengths[u]+=scale*s*s*k
                    for j in labels:counts[u,j]+=scale*s*s*N[j]
                for v in range(u+1,len(sq)):
                    dist[u,v]=dist.get((u,v),0)+scale*(s-sq[v])**2
            return
        a=(k+(sum((t+1)*(b+1) for t,b in enumerate(path)) if mode else 0))%n
        N2=N[:];N2[a]+=1
        for b in range(len(U)):
            weights=[s*(U[b] if a in cond else V[b]) for s,cond in zip(sq,family)]
            if any(weights):visit(path+(b,),weights,N2)
    visit((),[1]*len(family),[0]*n)
    for x in mass:ck(x==D**m,'total mass')
    for i in labels:ck(sum(counts[i,j] for j in labels)==lengths[i],'total cost')
    left=0
    for i in labels:
        for j in labels:
            if i==j:continue
            bridge=family.index({i,j})
            ck(dist[i,bridge] <= 7*h2*counts[i,j],'conditional Hellinger')
            hpair=dist[min(i,j),max(i,j)];left+=hpair
            ck(hpair <= 2*(dist[i,bridge]+dist[j,bridge]),'pointwise triangle')
    ck(left<=28*h2*sum(lengths.values()),'ordered-pair average')
    return leaves

def bracket(n,eta):
    cells=[1]*n+[0]*((1<<(n-1).bit_length())-n)
    l=0;cost=0
    while len(cells)>1:
        l+=1;new=[]
        for a,b in zip(cells[::2],cells[1::2]):
            if a and b:cost+=2*ceil(F(l+4)/eta)
            new.append(int(bool(a or b)))
        cells=new
    ck(1<=cost<=32*n/eta,'bracket sample bound')

def main():
    leaves=cases=0
    for n,m,mode in product((2,3,4),(3,5,7),(0,1)):
        for U,V in [((2,1,2),(1,2,2)),((2,1,0,2),(1,2,2,0)),((0,1),(1,0)),((1,2),(1,2))]:
            leaves+=one(n,m,mode,U,V);cases+=1
    print(f'{cases} seeded finite policies/law pairs, {leaves} terminal atoms including singular or identical laws: two-plant Hellinger and averaged counts verified exactly.')
    cases=0
    for n,eta in product(range(2,258),(F(1,997),F(2,9),F(1),F(19,10),F(2))):
        bracket(n,eta);cases+=1
    print(f'{cases} unequal / power-of-two bracket cost checks: PASS.')
if __name__=='__main__':main()
