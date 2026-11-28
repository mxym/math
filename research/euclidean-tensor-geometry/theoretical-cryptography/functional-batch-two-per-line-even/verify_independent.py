#!/usr/bin/env python3
"""Actual field recovery spans, orbit counts, and integer finite differences."""
from itertools import permutations, product
from math import comb, factorial


def model(a, s):
    q=1<<a
    modulus={2:0b111,3:0b1011}[a]

    def mul(x,y):
        ans=0
        while y:
            if y&1:
                ans ^= x
            y >>= 1
            x <<= 1
            if x&q:
                x ^= modulus
        return ans

    inv={x:next(y for y in range(1,q) if mul(x,y)==1) for x in range(1,q)}
    zero=(0,)*s

    def scale(t,v):
        return tuple(mul(t,z) for z in v)

    def add(u,v):
        return tuple(x^y for x,y in zip(u,v))

    def norm(v):
        return scale(inv[next(z for z in v if z)],v) if v!=zero else zero

    reps=[zero]+[v for v in product(range(q),repeat=s) if next((z for z in v if z),0)==1]
    idx={v:i for i,v in enumerate(reps)}
    return q,mul,reps,idx,scale,add,norm


def recover_all_small():
    q,_,L,idx,scale,add,norm=model(2,2)
    k=[L[0]]+[scale(2+i%2,v) for i,v in enumerate(L[1:])]
    assert all(x!=y for x,y in zip(L[1:],k[1:]))
    n=len(L)
    possible=[[{} for _ in range(n)] for _ in range(n)]
    for i,j in product(range(n),repeat=2):
        if i==j==0:
            continue
        aa=range(1,q) if i else (0,)
        bb=range(1,q) if j else (0,)
        for a,b in product(aa,bb):
            w=add(scale(a,L[i]),scale(b,k[j]))
            if w!=L[0]:
                possible[i][j].setdefault(idx[norm(w)],set()).add(w)
        for line, vectors in possible[i][j].items():
            assert vectors == {scale(t,L[line]) for t in range(1,q)}
    witnessed=set()
    for perm in permutations(range(n)):
        for selected in product(*(possible[i][j] for i,j in enumerate(perm))):
            assert perm[0]!=0 and perm.index(0)!=0
            witnessed.add(tuple(selected.count(c) for c in range(1,n)))
    all_lists={c for c in product(range(n+1),repeat=n-1) if sum(c)==n}
    assert witnessed==all_lists and len(witnessed)==210
    print("INDEPENDENT: all 210 PG(1,4) request histograms witnessed by actual field spans")


def integer_det(B):
    M=[row[:] for row in B]
    n=len(M)
    prev=sign=1
    for k in range(n-1):
        row=next((i for i in range(k,n) if M[i][k]),None)
        if row is None:
            return 0
        if row!=k:
            M[row],M[k]=M[k],M[row]
            sign=-sign
        pivot=M[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                z,r=divmod(pivot*M[i][j]-M[i][k]*M[k][j],prev)
                assert r==0
                M[i][j]=z
            M[i][k]=0
        prev=pivot
    return sign*M[-1][-1]


def coefficient_checks(a,s):
    q,mul,L,idx,scale,add,norm=model(a,s)
    n=len(L)
    N=n-1
    x,y=1,n-1
    base=[[[0]*n for _ in L] for _ in range(2)]
    for i,u in enumerate(L):
        for k,l in enumerate((x,y)):
            for t in range(1,q):
                v=norm(add(u,scale(t,L[l])))
                base[k][i][idx[v]]+=1
    I=[]
    for xi in L[1:]:
        bits=[]
        for v in (L[x],L[y]):
            z=0
            for a0,b0 in zip(xi,v):
                z ^= mul(a0,b0)
            bits.append(z==0)
        I.append(bits)

    cache={}
    def evaluate(u,v):
        if (u,v) not in cache:
            B=[[u*e+v*f for e,f in zip(er,fr)] for er,fr in zip(*base)]
            det=integer_det(B)
            prod=(-1)**N*(q-1)*(u+v)
            for ix,iy in I:
                prod*=u+v-q*(u*ix+v*iy)
            assert det==prod
            cache[u,v]=det
        return cache[u,v]

    # The mixed finite difference at 0 annihilates every other monomial of
    # the same total degree.  No coefficient is obtained from the product DP.
    out=[]
    for u in (0,1,2,3,n-1,n):
        v=n-u
        z=0
        for i in range(u+1):
            for j in range(v+1):
                z+=(-1)**(n-i-j)*comb(u,i)*comb(v,j)*evaluate(i,j)
        norm_coeff,rem=divmod(z,factorial(u)*factorial(v))
        assert rem==0 and norm_coeff
        m=comb(n,u)
        given=norm_coeff//((-1)**N*(q-1))
        assert norm_coeff==given*((-1)**N*(q-1))
        T=(q**(s-1)-1)//(q-1)
        assert (given-(1-q*T)*m)%((m & -m)*(1<<(2*a-1)))==0
        out.append(norm_coeff)
    assert len(out)==6
    return len(cache),len(out)


if __name__=="__main__":
    recover_all_small()
    for a,s in ((2,3),(3,2)):
        points,coeffs=coefficient_checks(a,s)
        print(f"INDEPENDENT: q={1<<a}, s={s}: {points} exact orbit determinants, {coeffs} finite-difference coefficients PASS")
