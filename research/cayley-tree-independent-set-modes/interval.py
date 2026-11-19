"""A rational stochastic enclosure for occupation at the Kesten-root (application to Cayley trees).
All probabilities are integer multiples of 1/M and magnitudes integer multiples of 1/K.
Standard library only; never rely on assert. See PROOF.md."""
from fractions import Fraction as F
from math import factorial
K=400
M=10**12
D=10
L=12
def atom(k):return {k:M}
def complete(counts,low):
    d={k:v for k,v in counts.items() if v}
    if any(v<0 for v in d.values()) or sum(d.values())>M:raise ValueError("invalid mass")
    filler=0 if low else K
    d[filler]=d.get(filler,0)+M-sum(d.values())
    return {k:v for k,v in d.items() if v}
def divide(X,Y,low): # independent X/(1+Y), already bracketed inputs
    cnt={}
    for i,px in X.items():
        for j,py in Y.items():
            u=i*K;v=K+j
            k=u//v if low else (u+v-1)//v
            cnt[k]=cnt.get(k,0)+px*py
    return complete({k:v//M for k,v in cnt.items()},low)
einv=sum(F((-1)**k,factorial(k)) for k in range(16)) # odd last term 15: ≤ e^-1
def ordinary(children,low):
    # conditional on the ordinary Poisson(1) number of independent child subtrees
    part=atom(K); mix={}
    for d in range(D+1):
        weight=einv/factorial(d)
        for k,pk in part.items():mix[k]=mix.get(k,0)+weight*pk
        if d<D:part=divide(part,children,low)
    return complete({k:v.numerator//v.denominator for k,v in mix.items()},low)
def q(mu):return sum(F(k*p,M*(K+k)) for k,p in mu.items())
def main():
    amin,smin=atom(0),atom(0)
    amax,smax=atom(K),atom(K)
    for h in range(1,L+1):
        amin,amax=ordinary(amax,True),ordinary(amin,False)
        smin,smax=divide(amin,smax,True),divide(amax,smin,False)
        lo,hi=q(smin),q(smax)
        print(h,lo*10**6//1,-((-hi*10**6)//1))
    if lo<=F(304,1000) or hi>=F(308,1000):raise ValueError("bracket not proved")
if __name__=='__main__':main()
