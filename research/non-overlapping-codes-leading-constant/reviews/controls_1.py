"""Independent exact tiny checks using full binary parse trees and graph cliques.
No original verifier functions are imported. All checks remain active under -O."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb
from random import Random

def check(b,msg):
    if not b: raise AssertionError(msg)

def trees(n):
    if n==1: return [(1,)]
    return [(n,l,r) for i in range(1,n) for l in trees(i) for r in trees(n-i)]
trees=lru_cache(None)(trees)

def cutoff_location(tree,N):
    while tree[1][0]>=N or tree[2][0]>=N:
        check(min(tree[1][0],tree[2][0])<N,'two heavy children')
        tree=max(tree[1:],key=lambda x:x[0])
    return tree[0]

def tree_examples(q,l,n,theta):
    alpha=F(l,q); gamma=max(alpha,1-alpha)
    @lru_cache(None)
    def mass(T,side):
        # side 0: assigned left; 1: right; 2: unconstrained root.
        if T[0]==1:return [alpha,1-alpha,1][side]
        weight=[theta[T[0]],1-theta[T[0]],1][side]
        return weight*mass(T[1],0)*mass(T[2],1)
    L=[F(0)]+[sum(mass(T,0) for T in trees(i)) for i in range(1,n)]
    R=[F(0)]+[sum(mass(T,1) for T in trees(i)) for i in range(1,n)]
    for N in range(n//2+1,n):
        true=[F(0)]*(n+1)
        for T in trees(n):
            true[cutoff_location(T,N)]+=mass(T,2)
        for h in range(N,n+1):
            # Enumerate *every* ordered composition of the positive-gap sequence,
            # equivalent to all internal subsets of the interval.
            K=F(0)
            for mask in range(1<<max(n-h-1,0)):
                path=[h]+[i for i in range(h+1,n) if mask>>(i-h-1)&1]
                if n>h: path.append(n)
                weight=F(1)
                for a,b in zip(path,path[1:]):
                    weight*=theta[a]*R[b-a]+(1-theta[a])*L[b-a]
                K+=weight
            seed=sum(L[i]*R[h-i] for i in range(1,N) if 1<=h-i<N)
            check(K<=(gamma if h<n else 1),'path sum cap')
            check(K*seed==true[h], 'tree grouping by unique first seed')
    return len(trees(n))

def brute_code(q,n):
    best=0
    for z in range(1,q):
        words=[w for w in product(range(q),repeat=n) if w[0]<z<=w[-1]
              and all(w[:k]!=w[-k:] for k in range(1,n))]
        compat=[]
        for v in words:
            bits=0
            for j,w in enumerate(words):
                if v!=w and all(v[:k]!=w[-k:] and w[:k]!=v[-k:] for k in range(1,n)):
                    bits|=1<<j
            compat.append(bits)
        def branch(mask,k):
            nonlocal best
            best=max(k,best)
            while mask and k+mask.bit_count()>best:
                b=mask&-mask
                mask ^= b
                branch(mask&compat[b.bit_length()-1],k+1)
        branch((1<<len(words))-1,0)
    return best

def int_recurrence(q,n):
    def f(l,r):
        h=len(l)
        s=sum(l[i]*r[h-i] for i in range(1,h))
        if h==n: return s
        return max(f(l+[j],r+[s-j]) for j in range(s+1))
    return max(f([0,p],[0,q-p]) for p in range(1,q))

def marker_counts(q,k,t,card,tail_len):
    # Prefix automaton counts avoiding P on a fresh string of given length; compare
    # all-orders inclusion-exclusion over placements, no independence assumption in automaton.
    P=set((0,)*k+(1,)+v+(1,) for v in list(product(range(q),repeat=t))[:card])
    L=k+t+2
    states={()}|{w[:i] for w in P for i in range(1,L)}
    def move(w,x):
        w=w+(x,)
        if w in P:return None
        while w not in states: w=w[1:]
        return w
    tr={s:[move(s,x) for x in range(q)] for s in states}
    d={s:int(not s) for s in states}
    for i in range(tail_len):
        e=dict.fromkeys(states,0)
        for s in states:
            for v in tr[s]:
                if v is not None:e[v]+=d[s]
        d=e
    m=tail_len-L+1;p=F(card,q**L)
    total=F(0)
    for j in range(m+1):
        a=m-(j-1)*(L-1)
        D=comb(a,j)*p**j if a>=j else 0
        total+=(-1)**j*D
    check(F(sum(d.values()),q**tail_len)==total,'automaton vs full-order avoidance')
    return 1

if __name__=='__main__':
    rs=Random(59111); nt=0
    for n in (7,8,9,10):
        for q,p in [(2,1),(3,2),(13,1),(13,12)]:
            theta=[F(rs.choice([0,1,3,9,12]),12) for _ in range(n+1)]
            nt+=tree_examples(q,p,n,theta)
    a=[(q,n,brute_code(q,n),int_recurrence(q,n)) for q,nn in ((2,9),(3,4),(4,3))
        for n in range(2,nn+1)]
    check(all(x==y for _,_,x,y in a),'conflict graph vs recurrence')
    ar=sum(marker_counts(q,k,t,c,d) for q,k,t in [(2,2,1),(2,3,2),(3,3,2)]
            for c in [1,q**t-1,q**t] for d in [19,37,59])
    print('PASS',nt,'weighted full binary trees checked at every strict halfway cutoff;')
    print('clique/recurrence:',[(q,n,x) for q,n,x,_ in a])
    print(ar,'integer automaton/full inclusion-exclusion counts (tail lengths through 59).')
