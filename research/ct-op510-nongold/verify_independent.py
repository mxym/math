#!/usr/bin/env python3
"""Verify by ranks, Walsh congruences, RREF flats and square-zero group algebra."""
from itertools import combinations
from pathlib import Path
from hashlib import md5, sha256
import sys

Q = 64
EXP = [1]
for j in range(1,63):
    x = EXP[-1]<<1
    EXP.append(x^(0x43 if x&64 else 0))
assert len(set(EXP))==63 and EXP[-1]<<1 ^ (0x43 if EXP[-1]<<1&64 else 0) == 1
LOG = {x:i for i,x in enumerate(EXP)}


def p(x,n):
    return EXP[LOG[x]*n%63] if x else 0


def m(x,y):
    return EXP[(LOG[x]+LOG[y])%63] if x and y else 0


def xor(values):
    z = 0
    for x in values:
        z ^= x
    return z


def tr(x):
    return xor(p(x,1<<j) for j in range(6))


def rank(rows):
    piv = {}
    for x in rows:
        while x:
            j = (x & -x).bit_length()
            if j not in piv:
                piv[j] = x
                break
            x ^= piv[j]
    return len(piv)


def graph_ideal_rank(table):
    # If X_i denotes translation by the i-th bit and Y_i=1+X_i,
    # coefficient[Y^s] is the sum of coefficient[X^t] for t containing s.
    coeff = [0]*(1<<12)
    for x,y in enumerate(table):
        coeff[(x<<6) | y] = 1
    for i in range(12):
        for s in range(1<<12):
            if not s>>i&1:
                coeff[s] ^= coeff[s^(1<<i)]
    nz = [s for s,c in enumerate(coeff) if c]
    return rank(sum(1 << (k|s) for s in nz if not k&s) for k in range(1<<12))


def beta(table,x,y):
    return table[0]^table[x]^table[y]^table[x^y]


def pi(table,masks):
    normals = [0]
    for x in range(1,Q):
        cols = [beta(table,x,1<<i) for i in range(6)]
        assert rank(cols)==5
        [b] = [b for b in range(1,Q) if all((masks[b]&z).bit_count()%2==0 for z in cols)]
        normals.append(b)
    return normals


def walsh_adjoint(normals,masks):
    result=[]
    for mu in masks:
        diffs=[-2*sum(1-2*((normals[x]>>j)&1) for x in range(Q) if (x&mu).bit_count()%2)
               for j in range(6)]
        assert all(x%8==0 for x in diffs)
        result.append(sum(((d//8)&1)<<j for j,d in enumerate(diffs)))
    return result


def rref_flats():
    for piv in combinations(range(6),4):
        free = [j for j in range(6) if j not in piv]
        opts = [(r,j) for r,i in enumerate(piv) for j in free if j>i]
        for c in range(1<<len(opts)):
            rows = [1<<i for i in piv]
            for z,(r,j) in enumerate(opts):
                if c>>z&1:
                    rows[r] ^= 1<<j
            space = [0]
            for r in rows:
                space += [x^r for x in space]
            for v in (0,1<<free[0],1<<free[1],(1<<free[0]) | (1<<free[1])):
                yield tuple(sorted(x^v for x in space))


def check_tables(table,masks,expected=None):
    # For both maps check bilinearity on every input, so rank gives APN.
    def quadratic(f):
        pairs=[(i,j,beta(f,1<<i,1<<j)) for i,j in combinations(range(6),2)]
        for x in range(Q):
            assert f[x] == f[0]^xor(f[0]^f[1<<j] for j in range(6) if x>>j&1)^xor(
                v for i,j,v in pairs if x>>i&1 and x>>j&1)
    quadratic(table)
    norms = pi(table,masks)
    eps=walsh_adjoint(norms,masks)
    quadratic(eps)
    assert all(rank(beta(eps,x,1<<j) for j in range(6))==5 for x in range(1,Q))
    fl = list(rref_flats())
    assert len(fl)==len(set(fl))==2604
    assert all(xor(norms[x] for x in f) for f in fl)
    if expected is not None:
        assert eps==expected
    return eps


def field_adj_polynomial():
    # Multiply x^{-3} by 1+Tr(a^{-1}x^{-3})(1+c), with
    # c=sum_{r=0,4,5}(a^3*x^9)^{2^r}. Pull out coefficients
    # indexed by the two-bit complements in the six-digit binary word.
    coeff = {3:1}
    for i in range(6):
        for r in (None,0,4,5):
            idx = (3+3*(1<<i)-(0 if r is None else 9*(1<<r)))%63
            aexp = -(1<<i) if r is None else 3*(1<<r)-(1<<i)
            if idx.bit_count()==2:
                coeff[idx] = coeff.get(idx,0)^EXP[aexp%63]
    return {d:c for d,c in coeff.items() if c}


def main():
    f=[p(x,3)^(EXP[62] if tr(m(EXP[3],p(x,9))) else 0) for x in range(Q)]
    pair=[sum(tr(m(u,1<<j))<<j for j in range(6)) for u in range(Q)]
    assert all(x in (0,1) for x in map(tr,range(Q)))
    assert len(set(pair))==Q
    pol=field_adj_polynomial()
    assert pol=={3:1,9:30,18:44}
    expected=[xor(m(c,p(x,k)) for k,c in pol.items()) for x in range(Q)]
    check_tables(f,pair,expected)
    assert graph_ideal_rank(f)==1146
    assert graph_ideal_rank([p(x,3) for x in range(Q)])==1102
    print("independent field: APN/adjoint polar ranks 5; all 2604 RREF flats nonzero;"
          " square-zero graph-ideal ranks 1146 (switched cube), 1102 (Gold)")
    print("independent field: exact adjoint coefficients", sorted(pol.items()))
    tri=[[1,2,4,8,16],[4,6,16,24],[8,5,37],[32,5],[3]]
    t=[0]*Q
    for x in range(1,Q):
        i=(x & -x).bit_length()-1
        y=x^(1<<i)
        t[x]=t[y]^xor(c for j,c in enumerate(tri[i] if i<5 else (), i+1) if y>>j&1)
    check_tables(t,range(Q))
    assert graph_ideal_rank(t)==1146
    print("independent row 2: APN/adjoint polar ranks 5;"
          " all 2604 RREF flats nonzero; square-zero graph-ideal rank 1146")
    if len(sys.argv)>1:
        data=Path(sys.argv[1]).read_bytes()
        assert len(data)==2235 and md5(data).hexdigest()=="f4035110834ac7b87553da3449e66790"
        assert sha256(data).hexdigest()=="74fba5a5b95d16a21bbafe262041a10ba0bec5c0e4120413315d3741fae478fe"
        lines=data.splitlines()
        assert len(lines)==13
        row2=[int(s,16) for s in lines[1].split(b",") if s]
        assert row2==t
        print("provenance: all 64 entries equal the authors' QAPN-6-6 row 2")
        catalog = []
        lin = [h for h in rref_flats() if 0 in h]
        assert len(lin)==651
        for row in lines:
            frow=[int(s,16) for s in row.split(b",") if s]
            assert len(frow)==64
            assert all(frow[x] == frow[0]^xor(frow[0]^frow[1<<j] for j in range(6) if x>>j&1)^xor(
                beta(frow,1<<i,1<<j) for i,j in combinations(range(6),2) if x>>i&1 and x>>j&1)
                for x in range(64))
            qrow=pi(frow,range(Q))
            bad=sum(not xor(qrow[x] for x in h) for h in lin)
            catalog.append((graph_ideal_rank(frow),bad))
        assert catalog == [(1172,7),(1146,0),(1102,0),(1168,7),(1170,8),(1170,10),
                           (1170,9),(1172,10),(1174,12),(1166,7),(1170,5),(1166,14),(1158,45)]
        print("dimension-six catalogue (graph-code rank, zero linear 4-flats):", catalog)

    print("PASS: independent rank, Walsh, RREF and group-algebra certificates")


if __name__=="__main__":
    main()
