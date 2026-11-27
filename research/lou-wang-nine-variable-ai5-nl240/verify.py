#!/usr/bin/env python3
"""Verify the Walsh and algebraic-immunity claims using exact arithmetic."""
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
N = 512
DEGREE4 = [x for x in range(N) if x.bit_count() <= 4]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def fwt(T):
    W = [1-2*x for x in T]
    h = 1
    while h < len(W):
        for i in range(0, len(W), 2*h):
            for j in range(i, i+h):
                a, b = W[j], W[j+h]
                W[j], W[j+h] = a+b, a-b
        h *= 2
    return W


def direct_fourier(T):
    return [sum(1-2*(v^((i&u).bit_count()&1)) for i,v in enumerate(T))
            for u in range(len(T))]


def rm_row(point):
    return sum(1<<i for i, a in enumerate(DEGREE4) if point & a == a)


def rank2(rows):
    basis = {}
    for w in rows:
        while w:
            p = w.bit_length()-1
            if p not in basis:
                basis[p] = w
                break
            w ^= basis[p]
    return len(basis)


def rotate(x):
    return (x & 0x180) | ((x << 1) & 127) | ((x >> 6) & 1)


def orbits(s):
    rem = set(s)
    O = []
    while rem:
        x = min(rem)
        o = [x]
        y = rotate(x)
        while y != x:
            o.append(y)
            y = rotate(y)
        require(set(o) <= rem, "non-invariant set under the seven-cycle")
        rem.difference_update(o)
        O.append(o)
    return O


def gf8mul(a,b):
    z=0
    while b:
        if b&1:
            z^=a
        b>>=1
        a<<=1
        if a&8:
            a^=0b1011
    return z


def powers(a):
    p=[1]
    for _ in range(6):
        p.append(gf8mul(p[-1],a))
    require(gf8mul(p[-1],a)==1,"not a seventh root")
    return p


def rank8(A):
    A = [v[:] for v in A]
    rank=0
    for c in range(len(A[0])):
        j=next((j for j in range(rank,len(A)) if A[j][c]),None)
        if j is None:
            continue
        A[rank],A[j]=A[j],A[rank]
        p=A[rank]
        inv=next(a for a in range(1,8) if gf8mul(a,p[c])==1)
        for row in A[rank+1:]:
            k=gf8mul(row[c],inv)
            if k:
                for i in range(c,len(row)):
                    row[i]^=gf8mul(k,p[i])
        rank+=1
    return rank


def block_ranks(points):
    R, C = orbits(points), orbits(DEGREE4)
    ans=[]
    for root in range(1,8):
        p=powers(root)
        ru=[r for r in R if root==1 or len(r)==7]
        cv=[c for c in C if root==1 or len(c)==7]
        M=[]
        for r in ru:
            x=r[0]
            row=[]
            for c in cv:
                z=0
                for k,u in enumerate(c):
                    if x&u==u:
                        z^=p[k]
                row.append(z)
            M.append(row)
        ans.append((rank8(M),len(ru),len(cv)))
    return ans


def main():
    H="".join((ROOT/"witness.txt").read_text().split())
    require(len(H)==128,"bad source word length")
    T=[(int(ch,16)>>i)&1 for ch in H for i in range(4)]
    require(len(T)==N and sum(T)==256,"not a balanced table")
    require(all(T[x]==T[rotate(x)] for x in range(N)),"bad seven-cycle convention")
    W=fwt(T)
    require(W==direct_fourier(T),"Walsh methods disagreed")
    nonzero=min(u.bit_count() for u in range(N) if W[u])
    require(nonzero==4 and max(map(abs,W))==32,"bad spectral parameters")
    print("Walsh histogram:",sorted(Counter(W).items()))
    print("Nonlinearity 240; resiliency 3; exact signed Walsh methods agree.")
    A=T[:]
    for i in range(9):
        for x in range(N):
            if x>>i&1:
                A[x]^=A[x^(1<<i)]
    deg=Counter(x.bit_count() for x,c in enumerate(A) if c)
    require(max(deg)==5,"bad ANF degree")
    print("ANF monomials by degree:",sorted(deg.items()))
    for a in (0,1):
        X=[x for x in range(N) if T[x]==a]
        rows=[rm_row(x) for x in X]
        first=rank2(rows)
        second=block_ranks(X)
        require(first==256,"degree-four annihilator exists")
        require(second==[(40,40,40)]+[(36,36,36)]*6,"rank blocks not all invertible")
        print(f"f={a}: full RM(4,9) rank {first}; seven spectral-block ranks {[r for r,_,_ in second]}.")
        require(rank2(rows[:-1]+[rows[0]])==255,"negative rank control did not fail")
    bad=T[:]
    bad[0]^=1
    require(fwt(bad)[0]!=0,"negative resiliency control did not fail")
    print("PASS duplicate-row and one-bit truth-table negative controls.")


if __name__=="__main__":
    main()
