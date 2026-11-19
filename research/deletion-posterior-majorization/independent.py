from itertools import product
from math import comb
from collections import Counter
def require(ok):
    if not ok:
        raise RuntimeError("exact deletion check failed")
def embeddings(x,y):
    # Dynamic programming by target prefixes, independent of column-alignment proof.
    dp=[1]+[0]*len(y)
    for ch in x:
        for i in range(len(y),0,-1):
            if y[i-1] == ch:
                dp[i]+=dp[i-1]
    return dp[-1]
checks=0
for q,N in ((2,8),(3,5)):
    for n in range(N+1):
        xs=list(product(range(q),repeat=n))
        for m in range(n+1):
            ref=sorted((embeddings(x,(0,)*m) for x in xs),reverse=True)
            want=sum(comb(n,k)*(q-1)**(n-k) for k in range(m,n+1))
            for y in product(range(q),repeat=m):
                a=sorted((embeddings(x,y) for x in xs),reverse=True)
                A=B=0
                for x,z in zip(a,ref):
                    A+=x
                    B+=z
                    require(A<=B)
                require(A==B==comb(n,m)*q**(n-m))
                require(sum(x>0 for x in a)==want)
                if 0<m<n and len(set(y))>1:
                    require(a[0]<ref[0] and sum(x*x for x in a)<sum(x*x for x in ref))
                checks+=1
print(f"{checks} exact complete posterior orders, masses or endpoint comparisons by independent DP; PASS")
