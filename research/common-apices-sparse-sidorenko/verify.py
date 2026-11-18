#!/usr/bin/env python3
"""Exact finite diagnostics for README.md, not a substitute for its inequalities."""
from fractions import Fraction as F
from itertools import product
from math import prod, ceil
from random import Random
from collections import Counter
import json

def chk(x, why):
    if not x: raise ValueError(why)

def hom(g, weights, n, edges):
    return sum(prod(weights[x] for x in xs)*prod(g[xs[i]][xs[j]] for i,j in edges)
               for xs in product(range(len(weights)),repeat=n))
def path(n):return tuple((i,i+1) for i in range(n))
def graph_apex(n,E,k):
    return tuple(E)+tuple((i,n+j) for i in range(n) for j in range(k))

def run(g,ww,den,k,graphs,direct=False):
    # Integer input: host block probabilities ww/sum(ww), edge probabilities g/den.
    pN=sum(ww); N=len(ww); a=2**(k-1)-1; L=F(4**k-1-3*k,9); b=F(16,3*k)*L
    cases=Counter()
    gs=[g,[[den-x for x in row]for row in g]]
    def box(n,E): # direct, integer brute-force hom density per color
        return F(2**(len(E)-1)*sum(hom(G,ww,n,E) for G in gs),pN**n*den**len(E))
    def fixed(n,E): # condition on BASE first: integrate out independent apices
        s=0
        for G in gs:
            for x in product(range(N), repeat=n):
                q=sum(ww[z]*prod(G[z][xx] for xx in x) for z in range(N))
                s+=prod(ww[xx]for xx in x)*prod(G[x[i]][x[j]] for i,j in E)*q**k
        ee=len(E)+k*n
        return F(s*2**(ee-1),pN**(n+k)*den**ee)
    star=fixed(1,()); Q=fixed(2,()); B=fixed(2,((0,1),))
    tri=box(3,((0,1),(0,2),(1,2)))
    A=sum(F(ww[i],pN)*(F(2*sum(w*x for w,x in zip(ww,g[i])),den*pN)-1)**2 for i in range(N))
    chk(tri==1+3*A and 1<=star<=1+a*A and B>=tri**k and 1<=Q<=1+b*(B-1),'moments')
    cases['moment checks']+=1
    if A==0:
        chk(star==1 and B==Q,'half-regular')
        cases['half-regular hosts and k']+=1
    cache={}
    for n,E in graphs:
        m=len(E); r=m-n+1; D=fixed(n,E)
        chk(D*star**(n-2)*Q**r>=B**m,'book '+str((k,g,n,E)))
        cases['book transfers']+=1
        if direct and n+k<=7:
            chk(D==box(n+k,graph_apex(n,E,k)),'direct full graph')
            cases['direct full graph crosschecks']+=1
        if r==0:continue
        for j in range(1,m//(r+1)+1):
            if j not in cache:cache[j]=fixed(j+1,path(j))
            P=cache[j]
            chk(P>=(1+A)**((k+1)*j+k-1),'path input')
            chk(D**j * star**(m-(r+1)*j)*Q**(r*j)>=P**m,'spectral transfer')
            cases['path transfers']+=1
        if (n-2)*F(a,3*k)+r*b<=m:
            chk(D>=1,'sharp sufficient region')
            cases['specialized theorem instances']+=1
        if A==0:chk(D>=B**(n-1),'regular strengthening')
    return cases
def main():
    c=Counter()
    graphs=[(2,((0,1),)),(4,path(3)),(4,path(3)+((3,0),)),(5,path(3)+((3,0),(0,4))),
        (6,path(5)+((5,0),)),(5,tuple((i,j) for i in range(2) for j in range(2,5))),
        (6,tuple((i,j) for i in range(3) for j in range(3,6)))]
    for a,b,d in product(range(3),repeat=3):
        for w in ([1,1],[1,2]):
            for k in (2,3,4,5,6):
                c.update(run([[a,b],[b,d]],w,2,k,graphs,direct=(k==2)))
    c['two-block weighted hosts']=54
    R=Random(7310381)
    for ii in range(21):
        n=3; den=7 if ii<20 else 2; G=[[1]*n for _ in range(n)]
        if ii<20:
            for i in range(n):
                for j in range(i,n):G[i][j]=G[j][i]=R.randint(0,den)
            ww=[R.randint(1,7)for _ in range(3)]
        else: G=[[0,1,2],[1,2,0],[2,0,1]]; ww=[1]*3
        for k in (2,3,5):c.update(run(G,ww,den,k,graphs,direct=ii<2 and k==2))
    c['three-block weighted hosts']=21
    const={k:{} for k in range(2,11)}
    for k in const:
        a=2**(k-1)-1; L=F(4**k-1-3*k,9); b=F(16,3*k)*L
        j=max(1,ceil(F(a-k+2,k+1)))
        C=2*a*b*j
        chk((k+1)*j+k-1-a>=1 and C>=2*j and C>=2*b,'constants')
        const[k]={'a':a,'b':str(b),'j':j,'ceil(C)':ceil(C)}
    print(json.dumps({'diagnostics':dict(c),'sufficient_constants':const},indent=2))
if __name__=='__main__':main()
