"""Exact rational checks for binary fibers and the (nonadditive) triple obstruction."""
from collections import Counter,defaultdict
from functools import lru_cache
from fractions import Fraction as Q
from itertools import product
from math import comb
from random import Random

def require(ok,msg):
    if not ok: raise ArithmeticError(msg)

def atanlog(x):
    z=(x-1)/(x+1); z2=z*z; term=z; s=Q(0)
    for j in range(12):
        s+=term/(2*j+1)
        term*=z2
    return 2*s,2*s+2*term/(25*(1-z2))

SCALE=10**12
L2,U2=atanlog(Q(2))
@lru_cache(None)
def loggrid(x):
    y=x;a=0
    while y<1:y*=2;a-=1
    while y>=2:y/=2;a+=1
    lo,hi=atanlog(y)
    if a>=0:lo+=a*L2;hi+=a*U2
    else:lo+=a*U2;hi+=a*L2
    return Q((lo*SCALE).__floor__(),SCALE),Q((hi*SCALE).__ceil__(),SCALE)

def bins(n,p):
    q=1-p;out=[]
    for k in range(n+1):
        w=p**k*q**(n-k); s=k/p-(n-k)/q; v=k/p**2+(n-k)/q**2
        out.append((w,w*s,w*(s*s-v)))
    return out

def upper_hess(counts,b):
    total=Q(0); wsum=Q(0);ddsum=Q(0)
    for cell,mult in counts.items():
        w,d,dd=(sum(b[k][j] for k in cell) for j in range(3))
        wsum+=mult*w;ddsum+=mult*dd
        lo,hi=loggrid(w)
        total+=mult*(-dd*(lo if dd>=0 else hi)-d*d/w)
    require(wsum==1 and ddsum==0,'grouped outputs')
    return total

def mat(seq):
    if not seq: yield []; return
    x=seq[0]
    for a in mat(seq[1:]):yield [[x]]+a
    for i in range(1,len(seq)):
        for a in mat(seq[1:i]+seq[i+1:]):yield [[x,seq[i]]]+a

def signature(G):
    return Counter(tuple(sorted(x.bit_count() for x in c)) for c in G)

def sharp(n):
    # Polynomial joint count of Hamming weights over a word and its two orbit partners.
    counts={(0,0,0):1}
    for _ in range(n//2):
        nxt=Counter()
        for v,a in counts.items():
            for cols in [(0,1,2),(1,2,0),(2,0,1),(1,1,1)]:
                nxt[tuple(i+j for i,j in zip(v,cols))]+=a
        counts=nxt
    # Each size-3 orbit represented three times in joint histogram. Remove exactly four words.
    for v in [(n//2,)*3,(0,n//2,n),(n//2,n,0),(n,0,n//2)]:
        counts[v]-=1
    C=Counter()
    for v,c in counts.items(): C[tuple(sorted(v))]+=c
    require(all(x%3==0 and x>=0 for x in C.values()),'orbit counts')
    C=Counter({v:k//3 for v,k in C.items() if k})
    C[(0,)]=1;C[(n,)]=1;C[(n//2,)]=2
    b=bins(n,Q(1,2)); ll=Q(0);cc=Q(0);ss=0
    for cell,mult in C.items():
        w,d,dd=(sum(b[k][j] for k in cell) for j in range(3))
        ss+=mult*w
        if len(cell)==3: ll-=mult*dd
        cc-=mult*d*d/w
    require(ss==1 and ll*2**n==8*n*(n-2) and cc*2**n==-8*n*n,'curvature integer coefficients')
    lo,hi=loggrid(Q(3)); require(cc+ll*lo>0 if n>=24 else cc+ll*hi<0,'threshold')

def main():
    rng=Random(564); trials=maps=0
    pp=[Q(1,100),Q(1,11),Q(1,5),Q(2,7),Q(3,8),Q(49,100),Q(1,2),Q(73,100)]
    for n in range(2,10):
        endpoints=[[0],[2**n-1]]; words=list(range(1,2**n-1)); maps0=[]
        if n<=3:maps0=[signature(endpoints+c) for c in mat(words)]
        else:
            for seed in range(9):
                rng.shuffle(words); cut=2*((len(words)//2)*seed//8)
                groups=[words[i:i+2] for i in range(0,cut,2)]+[[v] for v in words[cut:]]
                maps0.append(signature(endpoints+groups))
        # binary weights plus an additional unit bit
        a=[1]+[2**i for i in range(n-1)];G=defaultdict(list)
        for word in range(2**n): G[sum(w for i,w in enumerate(a) if (word>>i)&1)].append(word)
        require(max(map(len,G.values()))==2,'example fibers')
        maps0.append(signature(G.values()))
        for prob in pp:
            b=bins(n,prob)
            for C in maps0:
                require(upper_hess(C,b)<0,'nonnegative or unresolved H curvature')
                trials+=1
        maps+=len(maps0)
    for n in range(4,33,2):sharp(n)
    print(f'PASS: {maps} binary-fiber maps, {trials} rational curvatures via certified log intervals; 15 ternary orbit laws with exact integer coefficients (n=4,6,...,32).')
if __name__=='__main__': main()
