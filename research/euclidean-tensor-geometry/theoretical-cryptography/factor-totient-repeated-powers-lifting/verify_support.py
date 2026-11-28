from itertools import combinations,product
from math import gcd,prod,isqrt
from collections import Counter
P=(2,3,5,7,11,13,17)
def iroot(n,e):
    l,h=0,1<<((n.bit_length()+e-1)//e)
    while h-l>1:
        m=(l+h)//2
        if m**e<=n:l=m
        else:h=m
    return h if h**e==n else l
def prime(m):return m>=2 and all(m%d for d in range(2,isqrt(m)+1))
def classify(n,v):
    if v==1:return 0,1
    for e in range(1,n.bit_length()+1):
        x=iroot(v,e)
        if x**e==v and prime(x):return 1,x
    return 2,None
counts=Counter(); cases=Counter(); paths=Counter()
for k in range(1,6):
 for S in combinations(P,k):
    R=prod(S); F=prod(q-1 for q in S)
    H={p for p in S if any((q-1)%p==0 for q in S)}
    D0=prod(set(S)-H)
    for j in S:
        C=set(S)-{j}
        if C and min(C)>2 and max(C)<2*min(C) and j-1<min(C)**2 and j!=2:
            cases['one-outlier']+=1;assert len(H)<=1
    for E in product((1,2,3),repeat=k):
        n=prod(p**e for p,e in zip(S,E)); t=prod((p-1)*p**(e-1) for p,e in zip(S,E))
        d=n//gcd(n,t); v=n//gcd(n,pow(d,n.bit_length(),n)); assert d==D0
        assert v==prod(p**e for p,e in zip(S,E) if p in H)
        cl,h=classify(n,v); assert cl==min(2,len(H));counts[cl]+=1
        if cl<2:assert d*h==R and t*R//n==F and t*R%n==0
        if not H:continue
        e=max(j for p,j in zip(S,E) if p in H)
        if len(H)>1:paths['multi-hidden']+=1
        for p,j in zip(S,E):
            if p not in H or j!=e:continue
            a,b,y=1,0,p
            while y in H:
                q=min(s for s in S if (s-1)%y==0)
                mult=(q-1)//y;a,b,y=mult*a,mult*b+1,q
            assert y==a*p+b and d%y==0 and a<=max(S)//min(S)
            if gcd(a,d)!=1:continue
            mu=iroot(v,sum(j for q,j in zip(S,E) if q in H))
            C=mu+v*((b*pow(a*v,-1,d))%d)
            M=v*d**e;w=p-mu
            assert gcd(pow(w+C,e,M),M)%(p*y)**e==0
            assert abs(w)<=max(H)-min(H)
            paths['crt']+=1
print('classes',sorted(counts.items()),'finite one-outlier',dict(cases),'crt checks',dict(paths))
