#!/usr/bin/env python3
"""Exact finite checks of the crossing proof, revenue/surplus identity and sharp examples.
These finite checks are not proofs of the population or all-horizon results. No dependencies."""
from fractions import Fraction as F
from itertools import combinations_with_replacement as multisets, product, permutations
from math import factorial, comb

def require(test, context):
    if not test: raise ArithmeticError(context)

def mass(ps):
    a=[F(1)]
    for p in ps:
        b=[F(0)]*(len(a)+1)
        for i,ai in enumerate(a):
            b[i]+=ai*(1-p); b[i+1]+=ai*p
        a=b
    return a

def binmass(n,p):return [comb(n,j)*p**j*(1-p)**(n-j) for j in range(n+1)]
def A(k,j):return min(F(1),F(k,j+1))
def tail(b,k):return sum(b[k:])
def expect(b,f):return sum(p*f(j) for j,p in enumerate(b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def main():
    # Fix binomial parameters; solve the last heterogeneous parameter from the stockout equality.
    # This produces exactly matched nonuniform arrays rather than approximate quantiles.
    matched=cuts=degenerate=0
    grid=tuple(F(j,4) for j in range(5))
    for n in range(1,8):
        for pre in multisets(grid,n-1):
            prepm=mass(pre)
            for k in range(1,n+1):
                if prepm[k-1]==0:continue
                for p in (F(1,4),F(1,3),F(1,2),F(2,3),F(3,4)):
                    bm=binmass(n,p)
                    last=(tail(bm,k)-tail(prepm,k))/prepm[k-1]
                    if not 0<=last<=1:continue
                    ps=tuple(pre)+(last,);pm=mass(ps)
                    require(tail(pm,k)==tail(bm,k),"missed cut")
                    ratios=[u/v for u,v in zip(pm,bm)]
                    require(all(ratios[j]**2>=ratios[j-1]*ratios[j+1] for j in range(1,n)),"Newton")
                    for d in range(n+1):
                        delta=sum(pm[:d+1])-sum(bm[:d+1])
                        require(delta<=0 if d<k else delta>=0,(n,k,d,"CDF"))
                        cuts+=1
                    require(expect(pm,lambda j:min(k,j))>=expect(bm,lambda j:min(k,j)),"UT")
                    require(expect(pm,lambda j:A(k,j))>=expect(bm,lambda j:A(k,j)),"AR")
                    matched+=1;degenerate+=any(x in (0,1) for x in ps)
    # Multiplicity ties: enumerate the full distribution, independent Bernoulli tie coins, and all orders.
    theta=F(2,5);t=F(1)
    laws=(((0,F(1,3)),(1,F(1,2)),(4,F(1,6))),((1,F(2,3)),(5,F(1,3))),
          ((0,F(1,4)),(1,F(3,4))),((1,F(1,2)),(2,F(1,2))))
    n=len(laws);cases=0
    def expand(law):
        res=[]
        for v,p in law:
            if v==t:res.extend([(v,0,p*(1-theta)),(v,1,p*theta)])
            else:res.append((v,int(v>t),p))
        return res
    states=list(product(*map(expand,laws)));orders=list(permutations(range(n)))
    ps=[sum(p*eligible for _,eligible,p in expand(l)) for l in laws]
    sur=[sum(p*max(v-t,0) for v,p in law) for law in laws]
    for k in range(1,n+1):
        online=F(0);off=[F(0)]*(n+1)
        for st in states:
            P=F(1); vals=[s[0] for s in st]
            for v,e,x in st:P*=x
            for order in orders:
                sel=[i for i in order if st[i][1]][:k]
                online+=P*sum(vals[i] for i in sel)/len(orders);cases+=1
            for ell in range(1,n+1):off[ell]+=P*sum(sorted(vals,reverse=True)[:ell])
        util=expect(mass(ps),lambda j:min(k,j))
        acc=[expect(mass(ps[:i]+ps[i+1:]),lambda j:A(k,j)) for i in range(n)]
        require(online==t*util+dot(sur,acc),"leave-one-out identity")
        for ell in range(1,n+1):
            require((online/k)/(off[ell]/ell)>=min(util/k,F(ell,k)*min(acc)),"welfare")
    # Exact finite rational giant witnesses with n-1 competitors q=p-eps, whose rare distinguished
    # qualification is solved from the prescribed stockout probability; high value M=eta^{-2}.
    # Unlike the atomless construction in the text the following uses simple binary discrete laws.
    giant=0
    for n in range(2,9):
        for k in range(1,n):
            for p in (F(1,3),F(1,2),F(2,3)):
                phi=tail(binmass(n-1,p),k)
                for h in (F(1,256),F(1,1024)):
                    q=p-h; b=binmass(n-1,q);delta=(phi-tail(b,k))/b[k-1]
                    require(0<delta<1 and tail(mass((q,)*(n-1)+(delta,)),k)==phi,"giant calibration")
                    m=1/delta**2
                    prob=expect(b,lambda j:A(k,j))
                    # Exact welfare from competitors of value 2 or 0 and distinguished value M or 0, price 1.
                    sm=F(0)
                    for j,bj in enumerate(b):
                        sm+=bj*((1-delta)*min(k,j)*2+delta*min(F(1),F(k,j+1))*(2*j+m))
                    require(delta*m*prob<=sm<=delta*m*prob+2*n,"giant online remainder")
                    for ell in range(1,n+1):
                        off=expect(b,lambda j:(1-delta)*min(j,ell)*2+delta*(m+min(j,ell-1)*2))
                        require(delta*m<=off<=delta*m+2*n,"giant prophet remainder")
                    giant+=1
    print(f"PASS: {matched} exactly stockout-matched binomial comparisons ({degenerate} include 0/1 biases); {cuts} cumulative comparisons.")
    print(f"PASS: {cases} value/tie/order/capacity cases checked against leave-one-out welfare formula.")
    print(f"PASS: {giant} finite exact-welfare rare-giant instances at prescribed stockout, all benchmark capacities.")
if __name__=='__main__':main()
