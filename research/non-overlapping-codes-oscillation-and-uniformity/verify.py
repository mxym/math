"""Finite, exact stress tests (standard library); not evidence of priority or a replacement for the analytic proof."""
from itertools import product
from math import comb
from fractions import Fraction as F


def ck(flag, msg):
    if not flag: raise ArithmeticError(msg)


def run_free(q,k,t):
    # Finite automaton records trailing run length; scalar recurrence for long lengths separately below.
    state=[1]+[0]*(k-1)
    for _ in range(t): state=[(q-1)*sum(state)]+state[:-1]
    return sum(state)


def count(q,k,t):
    a=[q**i for i in range(min(k,t+1))]
    if t<k: return a[-1]
    a.append(q**k-1)
    for i in range(k+1,t+1):
        a.append(q*a[-1]-(q-1)*a[i-k-1])
    return a[t]


def best(q,n):
    # This is a global maximum; the monotone cap prunes the entire unused suffix of k.
    top=-1; keys=[]; cap=(q-1)**2*q**(n-4)
    for k in range(2,n-1):
        if cap<top: break
        z=(q-1)**2*count(q,k,n-k-2)
        ck(0 < z <= cap, ('one-run cap',q,k,n))
        if z>top: top=z; keys=[k]
        elif z==top: keys.append(k)
        cap//=q
    return tuple(keys),n*top*10**6//q**n


def non_overlap(words,n):
    for t in range(1,n):
        left={w[:t] for w in words}
        ck(not any(w[-t:] in left for w in words), ('overlap',n,t))


def marker_test(q,r,I,L,n):
    sigma=range(q); R=r+1
    anc=lambda w: len(w)==R and w[:-1]==(0,)*r and w[-1] in I
    end=lambda x: (x!=0 if r else x not in I)
    A=sorted(w for w in product(sigma,repeat=L) if anc(w[:R]) and end(w[-1]) and
             not any(anc(w[i:i+R]) for i in range(1,L-R+1)))
    ck(A,('empty custom dictionary',q,r,L)); non_overlap(A,L)
    # Lexicographically alternate markers to test an arbitrary genuine sub-dictionary.
    P=set(A[::2]); valid=[]; hist={}
    for w in product(sigma, repeat=n):
        occ=[i for i in range(n-L+1) if w[i:i+L] in P]
        hist[len(occ)]=hist.get(len(occ),0)+1
        if occ==[0] and end(w[-1]) and not any(anc(w[n-d:n-d+R]) for d in range(R,L)):
            valid.append(w)
    ck(valid,('empty toy code',q,r,L)); non_overlap(valid,n)
    M=n-L+1; p=F(len(P),q**L)
    for j in range(M+1):
        actual=F(sum(comb(v,j)*c for v,c in hist.items() if v>=j),q**n)
        u=M-(j-1)*(L-1)
        predicted=comb(u,j)*p**j if u>=j else 0
        ck(actual==predicted,('hard-core moments',M,L,j))
    return len(P),len(valid),q**n


def rounding(q,n):
    # All floor/ceil logarithms and alphabet sizes are integer comparisons.
    r=0; v=q
    while 8*v <= n: r+=1; v*=q
    Q=1; L=0
    while Q<n*n: Q*=q; L+=1
    Q*=q*q; L+=2
    s=min(q-1,(8*v+n-1)//n); d=F(s,v)
    b=F(q-1,q) if r else 1-d
    ck(4<=n*d<=16 and r+1<L and Q==q**L and Q>=n*n,('short marker',q,n))
    ck(n*F(Q//n,Q)>=1-F(1,n),('final dictionary discretization',q,n))
    if n>=10000: ck(b>=F(1,2) and d*(b-L*d)>F(1,n),('marker capacity',q,n))


def go():
    auto=0
    for q in range(2,8):
        for k in range(2,10):
            for t in range(35):
                ck(count(q,k,t)==run_free(q,k,t),('automaton',q,k,t)); auto+=1
    print('One-run finite automaton/scalar recurrence:',auto,'exact comparisons.')
    direct=0
    for q in (2,3,4):
        for n in range(4,8):
            allw=list(product(range(q),repeat=n))
            for k in range(2,n-1):
                target=sum(w[:k]==(0,)*k and w[k]!=0 and w[-1]!=0 and
                           not any(w[i:i+k]==(0,)*k for i in range(k+1,n-k)) for w in allw)
                ck(target==(q-1)**2*count(q,k,n-k-2),'direct class enumeration'); direct+=1
    print('Direct q-ary one-run classes:',direct)
    for q,n0,n1 in ((2,4096,5678),(3,3281,5406),(4,1365,2524),(8,4681,11124)):
        print('Global peak/trough samples q=',q,[(n,*best(q,n)) for n in (n0,n1)],'floor(normalized size x 10^6)')
    tests=[(2,2,{1},4,12),(3,1,{1},4,9),(3,1,{1,2},3,9),(3,0,{1},3,9),(4,0,{1,2},3,8),(3,2,{1},4,9)]
    for q,r,I,L,n in tests:
        print('Finite non-overlap, factorial moments',q,r,sorted(I),L,n,marker_test(q,r,I,L,n))
    grid=0
    for n in (16,17,31,127,1024,9999,10000,10001,10**6,10**11+89,10**24):
        for q in sorted({2,3,4,5,8,17,127,1000,10**9,n//8,max(2,n//8-1),n//8+1,n,n+1,n*n}):
            if q>=2: rounding(q,n); grid+=1
    print('Exact alphabet/length rounding pairs:',grid)
    ck(1+F(2,7)+F(2,49)>F(64,49),'q=8 exponential certificate')
    print('PASS: exact checks only; no floating-point or numerical optimization.')


if __name__=='__main__': go()
