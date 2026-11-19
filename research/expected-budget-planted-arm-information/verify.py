#!/usr/bin/env python3
"""Exact stopped-tree and noiseless-partition checks, standard library only.
These finite checks illustrate the proof; they do not replace its quantifiers.
"""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict

def ck(condition, message):
    if not condition:
        raise ArithmeticError(message)

def noisy(n, delta, horizon, policy):
    low=(1-delta)/2; high=1-low; r=high/low
    K=F(0); qp=[F(0)]*n; eq=ep=qb=pb=totalp=totalq=F(0); leaves=lost=0
    projected=defaultdict(lambda:[F(0)]*n)
    weights={}
    def node(history, scores, qmass, ancestor):
        nonlocal K,eq,ep,qb,pb,leaves,lost,totalq,totalp
        L=[r**x for x in scores]; avg=sum(L)/n
        length=len(history)
        stop=(length==horizon or (policy==1 and length>=2 and history[-2:]==(1,1)) or
              (policy==2 and length>=3 and sum(history)%4==2))
        if policy==0: a=length % n
        elif policy==1: a=(length + sum((j+1)*v for j,v in enumerate(history))) % n
        else: a=max(range(n), key=lambda j:(scores[j],(j-length-1)%n))
        if ancestor is None and (avg<=F(1,4) or stop):
            ancestor=history; weights[history]=[qmass*x for x in L]
            K-=qmass*sum(scores)/n
            totalq+=qmass;totalp+=qmass*avg
            eq+=qmass*length;ep+=qmass*avg*length
            if avg<=F(1,4): qb+=qmass;pb+=qmass*avg
            leaves+=1
        if stop:
            for j in range(n):
                projected[ancestor][j]+=qmass*L[j]
                qp[j]+=qmass*L[j]
            lost+=int(ancestor!=history)
            return
        if ancestor is None:
            ck(avg>F(1,4),'invalid prebarrier')
        for b in (0,1):
            new=list(scores);new[a]+=2*b-1
            node(history+(b,),new,qmass*(low if b else high),ancestor)
    node((),[0]*n,F(1),None)
    ck(totalp==totalq==1 and all(x==1 for x in qp),'mass')
    ck(weights==dict(projected),'full-to-stopped pushforward')
    ck(pb<=qb/4 and eq<=4*ep,'barrier/cost')
    ck(K==delta*eq/n,'reverse-KL exact coefficient of log r')
    return leaves,int(pb>0),lost

def noiseless(n):
    cases=0
    for depth in range(n+2):
        for kind in range(8):
            def run(j):
                hist=[];a=0
                while len(hist)<depth:
                    k=len(hist)
                    if kind&4 and k>1 and (hist[-1][1] or k==n+1):break
                    if kind&1:a=(a+(2 if k%3==0 else 0)+(hist[-1][1] if k else 0))%n
                    else:a=(k + ((1+sum(b for _,b in hist)) if kind&2 else 0))%n
                    hist.append((a,int(a==j)))
                return tuple(hist)
            null=run(None);labels=list(dict.fromkeys(a for a,b in null));d=len(labels)
            trans=[run(j) for j in range(n)]
            hist=sorted([trans.count(h) for h in set(trans)])
            expect=sorted([1]*d+([n-d] if n>d else []))
            ck(hist==expect, 'partition on seeded deterministic all-null path')
            cost=F(sum(map(len,trans)),n); c=F(d)-F(d*(d-1),2*n)
            ck(cost>=c,'noiseless path cost')
            cases+=1
    return cases

def slopes(n):
    """Certify consecutive incremental entropy slopes by integer products.
    e^(r h(1/r))=r^r/(r-1)^(r-1); clear denominators for r,r+1.
    """
    for r in range(2,n):
        # [r^r/(r-1)^(r-1)]^(r+1) >= [(r+1)^(r+1)/r^r]^r
        ck(r**(r*(2*r+1)) >= (r-1)**(r*r-1)*(r+1)**(r*(r+1)),'slope comparison')

def main():
    stats=[0]*3; trees=0
    for n,delta,h,p in product((2,3,4),(F(1,3),F(1,2),F(3,5),F(3,4)),(3,7,9),(0,1,2)):
        row=noisy(n,delta,h,p)
        trees+=1
        for i,x in enumerate(row):stats[i]+=x
    ck(stats[1]>0 and stats[2]>0,'crossing and lost continuation must occur')
    print(f'{trees} planted trees; {stats[0]} stopped atoms; {stats[1]} trees with nonzero barrier mass; {stats[2]} strict continuation atoms.')
    print('Exact mass, prefix pushforward, dummy/planted barrier costs, and reverse-KL log coefficients: PASS.')
    cases=sum(noiseless(n) for n in range(2,25)); slopes(80)
    print(f'{cases} noiseless deterministic trees with secret-dependent stops/repeats: exact partition and cost PASS.')
    print('Exact incremental entropy-slope comparisons through n=80: PASS.')
if __name__=='__main__':main()
