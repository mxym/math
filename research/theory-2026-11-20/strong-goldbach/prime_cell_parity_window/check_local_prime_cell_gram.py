"""Finite controls for the local Gram, not a proof of the asymptotic prime input."""
from math import isqrt
from itertools import combinations

def ck(b):
    if not b: raise RuntimeError("failed control")
def rank(cols):
    piv={}
    for v in cols:
        while v:
            j=v.bit_length()-1
            if j not in piv:
                piv[j]=v
                break
            v^=piv[j]
    return len(piv)
def primes(T):
    f=[True]*(T+1); f[0]=f[1]=False
    for p in range(2,isqrt(T)+1):
        if f[p]: f[p*p::p]=[False]*((T-p*p)//p+1)
    return [n for n in range(3,T+1) if f[n]]
def main():
    blocks=edges=subsets=even_anchor=odd_other=0; example=None
    for T in [700,701,998,999,1800,3503,8192]:
        h=(T//4)-5; L=h//2; ps=primes(T); mask=(1<<(L+1))-1
        for q in [13,27,37,65]:
            P={p%q for p in ps if h<=4*(T-2*p) and 3*(T-2*p)<=h}
            P=sorted(P)
            members={a:[p for p in ps if p%q==a] for a in P}
            anchor={a:next(p for p in members[a] if h<=4*(T-2*p) and 3*(T-2*p)<=h) for a in P}
            R={}; adj=set()
            for a in P:
                mid={T-2*p for p in members[a] if 0<=T-2*p<=2*L}
                bits=sum(1<<j for j in mid)
                r=rank([(bits>>i)&mask for i in range(L+1)])
                ck(r>0)
                # Local Gram block agrees with Frobenius; direct full ordered counts.
                d=[0]*(h+1)
                for p in members[a]:
                    for t in members[a]:
                        k=T-p-t
                        if 0<=k<=h: d[k]^=1
                ck(set(i for i in range(2*L+1) if d[i])==mid)
                blocks+=1; R[a]=r
            hits={}
            for a,b in combinations(P,2):
                cnt=[0]*(h+1)
                for p in members[a]:
                    for s in members[b]:
                        k=T-p-s
                        if 0<=k<=h: cnt[k]+=1
                ns={T-i for i,c in enumerate(cnt) if c%2}
                if ns: adj.add((a,b))
                for n in ns: hits.setdefault(n,[]).append((a,b))
                anchored=anchor[a]+anchor[b]
                if cnt[T-anchored]%2==0:
                    even_anchor+=1
                    if example is None: example=(T,h,q,a,b,anchored,cnt[T-anchored])
                if ns-{anchored}: odd_other+=1
                edges+=1
            for n,ls in hits.items():
                ck(len(set([v for edge in ls for v in edge]))==2*len(ls))
            for z in range(min(len(P),4)+1):
                for U in combinations(P,z):
                    if not any(e in adj for e in combinations(U,2)):
                        ck(sum(R[a] for a in U)<=T+1)
                    subsets+=1
    ck(even_anchor and odd_other)
    print("PASS blocks",blocks,"cells",edges,"hereditary subsets",subsets,"even full count at an actual anchor sum",even_anchor,"odd other centers",odd_other,"example (T,h,q,a,b,N,count)",example)
main()
