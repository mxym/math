"""Independent small binary field checks. No external packages. The general proof is analytic."""
from itertools import combinations
from functools import reduce
from operator import xor

def ck(v):
    if not v: raise RuntimeError("check failed")

def exists_space(eligible, n, k):
    # Each subspace has a unique reduced binary echelon basis with strictly increasing
    # highest bits, and these pivot bits cleared from the other rows.
    def rec(V, more):
        if more == 0: return True
        if len(V)<(1<<more)-1: return False
        Vset=set(V)
        for i,x in enumerate(V):
            p=x.bit_length()-1
            if p > n-more: break
            if more==1: return True
            b=1<<p
            nxt=[y for y in V[i+1:] if y>=2*b and not (y&b) and x^y in Vset]
            if rec(nxt,more-1): return True
        return False
    return rec(sorted(eligible),k)

def graph(S,m):
    n=2*m
    w=[int(v in S) for v in range(1<<n)]
    for j in range(n):
        h=1<<j
        for i in range(0,len(w),2*h):
            for k in range(i,i+h):w[k],w[k+h]=w[k]+w[k+h],w[k]-w[k+h]
    ck(w[0]==len(S)==1<<m)
    return exists_space([i for i in range(1,len(w)) if w[i]==0],n,m)

def check(m,poly):
    q=1<<m
    def mul(a,b):
        c=0
        while b:
            if b&1: c^=a
            b>>=1;a<<=1
            if a&q: a^=poly
        return c
    M=[[mul(i,j) for j in range(q)]for i in range(q)]
    def trace(x):
        z=0;a=x
        for _ in range(m):z^=a;a=M[a][a]
        ck(a==x and z in (0,1));return z
    t=[trace(x) for x in range(q)];d=t.index(1)
    def em(x,y):
        a,b=divmod(x,q);c,e=divmod(y,q)
        ac=M[a][c]
        return (ac^M[a][e]^M[b][c])*q+(M[b][e]^M[d][ac])
    def norm(x):
        a,b=divmod(x,q)
        return M[d][M[a][a]]^M[a][b]^M[b][b]
    E=range(q*q);C=[x for x in E if norm(x)==1];T=set(C)|{0}
    ck(len(C)==q+1 and reduce(xor,C,0)==0)
    Q=[t[norm(x)] for x in E]
    trmask=[sum(t[em(h,1<<j)//q]<<j for j in range(2*m)) for h in E]
    ck(len(set(trmask))==q*q)
    for h in E:
        w=sum((trmask[h]&x).bit_count()%2 for x in C)
        ck(w%2==0 and (w*(w-1)//2)%2==Q[h])
    ck(sum((-1)**v for v in Q)==-q)
    # The computational graph search uses ordinary bit dot product, not the tower trace basis.
    ck(graph({q*x+M[x][M[x][x]] for x in range(q)},m))
    # Generate only hole orbit representatives, but explicitly cover all two-subsets.
    todo=set(combinations(sorted(T),2)) if not m%2 or m==2 else {(0,x) for x in C}
    expected=len(todo);tested=0;orbs=0
    while todo:
        key=min(todo)
        orbit=set()
        a,b=key
        for _ in range(2*m):
            for c in C: orbit.add(tuple(sorted((em(a,c),em(b,c)))))
            a,b=em(a,a),em(b,b)
        ck(orbit<=todo);todo-=orbit;tested+=len(orbit);orbs+=1
        yes=graph(T-set(key),m);ck(yes==(m==2))
    ck(tested==expected)
    print("m=%d: trace identity at all %d dual vectors; %d hole pairs in %d orbits; graph positive control passed."%(m,q*q,tested,orbs))

if __name__=="__main__":
    for m,p in [(2,7),(3,11),(4,19),(5,37),(6,67)]: check(m,p)
