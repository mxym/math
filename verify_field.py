#!/usr/bin/env python3
"""Small-field original trace rank and exhaustive three-way comparison of every spectral mask."""
if not __debug__:
    raise SystemExit("Use ordinary Python, not python -O: proof assertions must run")
from functools import lru_cache
from itertools import combinations,product

def check(n,mod):
    q=1<<n; N=q-1
    def mul(a,b):
        z=0
        while b:
            if b&1:z^=a
            b>>=1; a<<=1
            if a>=q:a^=mod
        return z
    def power(a,k):
        z=1
        while k:
            if k&1:z=mul(a,z)
            k//=2; a=mul(a,a)
        return z
    assert len({power(2,i) for i in range(N)})==N
    def trace(a):
        z=0
        for _ in range(n):z^=a; a=mul(a,a)
        assert z in (0,1); return z
    tr=[trace(a) for a in range(q)]; T=[sum(tr[mul(a,1<<j)]<<j for j in range(n)) for a in range(q)]
    def coef(x,y):return mul(x^y,power(power(x,6)^power(y,6),q-2))
    piv={};pairs=0
    for x,y in combinations(range(q),2):
        pairs+=1;u=coef(x,y);assert tr[mul(u,power(x,5)^power(y,5))]==1
        for j in range(n):
            C=1<<j; h=mul(mul(C,C),x^y)^mul(C,power(x,3)^power(y,3));assert not tr[mul(u,h)]
        r=(T[u]<<((y-1)*n))^((T[u]<<((x-1)*n)) if x else 0)
        while r:
            j=r.bit_length()-1
            if j not in piv:piv[j]=r;break
            r^=piv[j]
    assert len(piv)==n*(q-2)
    # For every e, extract the literal n Frobenius-trace summands from the original
    # pair equation at x=r*y. For binary masks only, collect F_q entry-rows into
    # n GF(2) bit-rows directly; no rational inversion sequence or threshold.
    def all_masks(rows):
        p={}
        for v in rows:
            while v:
                h=v.bit_length()-1
                if h not in p:p[h]=v;break
                v^=p[h]
        return {b for b in range(q) if all((b&v).bit_count()%2==0 for v in p.values())}
    # Direct cyclic path oracle, on the fixed n-word, disjoint from threshold test.
    S=list(product(range(3),range(3),range(2))); step={}
    for z in range(4):
        for h,(u,v,c) in enumerate(S):
            row=[]
            for x,y in product(range(2),repeat=2):
                a=x+y+c
                if a%2!=z//2:continue
                A=3*x+u; B=3*y+v
                row.append((S.index((A//2,B//2,a//2)),(z&1)*((A==5)^(B==5))))
            step[z,h]=row
    @lru_cache(None)
    def rel(word):
        if not word:return tuple((1<<i,0) for i in range(18))
        z=word[0];m=rel(word[1:]);out=[]
        for h in range(18):
            (a,p),(d,j)=step[z,h];out.append((m[a][p]|m[d][j],m[a][1-p]|m[d][1-j]))
        return tuple(out)
    counts=0;K=pow(6,-1,N);frob=[pow(2,-t,N) for t in range(n)]
    for e in range(N):
        g=e*K%N; I=[((e*s+4)%N)+1 for s in frob]; raw={N}
        for r in range(q):
            if r==1:continue
            cols=[power(mul(coef(r,1),power(r,i)^1),1<<t) for t,i in enumerate(I)]
            for j in range(n):raw.add(sum(((z>>j)&1)<<t for t,z in enumerate(cols)))
        ker1=all_masks(raw)
        hk=lambda k:sum((s*k%N<K)<<t for t,s in enumerate(frob))
        ker2=all_masks({N}|{hk(k)^hk((g-k)%N) for k in range(N)})
        ker3=set()
        for b in range(q):
            if b.bit_count()%2:continue
            z=tuple(2*((g>>i)&1)+((b>>((i+1)%n))&1) for i in range(n));m=rel(z)
            if not any((p[1]>>i)&1 for i,p in enumerate(m)):ker3.add(b)
        known={0}|{(1<<s)^(1<<((s+1)%n)) for s in range(n) if e==(-4*(1<<s))%N}
        assert ker1==ker2==ker3==known,(n,e,ker1,ker2,ker3,known)
        counts+=len(ker1)-1
    print(f'n={n}: all {pairs} original pairs, rank={len(piv)} nullity={n}; {N*q} spectral (e,b) masks, {counts} nonzero; trace=threshold=automaton PASS')

if __name__=='__main__':
    for n,mod in [(3,11),(5,37),(7,131)]:check(n,mod)
