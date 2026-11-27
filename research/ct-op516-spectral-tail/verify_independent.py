#!/usr/bin/env python3
"""Independent Walsh, plane-parity and Cayley-graph regression checks."""
from collections import Counter
from itertools import combinations, product
from hashlib import md5, sha256
from pathlib import Path
import sys


def ip(x,y):
    return (x&y).bit_count()%2


def walsh(w):
    for n in (1<<j for j in range((len(w)-1).bit_length())):
        for i in range(0,len(w),2*n):
            for j in range(i,i+n):
                a,b=w[j],w[j+n]
                w[j],w[j+n]=a+b,a-b
    return w


def gf16_cube():
    z=[1]
    for j in range(14):
        x=z[-1]<<1
        z.append(x^0x13 if x>=16 else x)
    assert len(set(z))==15
    logs={v:i for i,v in enumerate(z)}
    return [0]+[z[(3*logs[x])%15] for x in range(1,16)]


def row11():
    c=[[1,2,4,8,16],[4,6,16,26],[8,5,53],[32,39],[62],[]]
    F=[0]*64
    for x in range(1,64):
        j=(x&-x).bit_length()-1
        y=x^(1<<j)
        F[x]=F[y]
        for i,val in enumerate(c[j],j+1):
            if y>>i&1:F[x]^=val
    return F


def odd_planes(F,H):
    vals=set()
    for x,y in combinations(H,2):
        if x^y>y:
            t=F[x]^F[y]^F[x^y]^F[0]
            if t in vals:vals.remove(t)
            else:vals.add(t)
    assert 0 not in vals
    return vals


def check_f(F):
    N=len(F); n=(N-1).bit_length()
    D=[[F[x]^F[x^a] for x in range(N)] for a in range(N)]
    assert all(all(row.count(v)==2 for v in set(row)) for row in D[1:])
    sem=[]
    all_rad={}
    for b in range(1,N):
        w=walsh([1-2*ip(b,x) for x in F])
        amplitude=max(map(abs,w))
        rad=tuple(a for a,row in enumerate(D) if len({ip(b,x) for x in row})==1)
        assert 2**n*len(rad)==amplitude**2
        if amplitude==2**(n//2+1):
            assert len(rad)==4
            sem.append(b)
        all_rad[b]=rad
    dists=Counter(len(r) for r in all_rad.values())
    assert dists==(Counter({1:10,4:5}) if n==4 else Counter({1:46,4:16,16:1}))
    assert odd_planes(F,range(1,N))==set(range(1,N))
    for u in range(N):
        m_parity=odd_planes(F,[x for x in range(1,N) if not ip(u,x)])
        s=[b for b in sem if any(ip(u,r) for r in all_rad[b])]
        assert not len(s)%4
        E=0
        for b in s:E^=b
        assert all(ip(E,v)==(v not in m_parity) for v in range(1,N))
    print("independent APN",n,"Walsh/derivative radical sizes",sorted(dists.items()),
          "and all adjoint parity entries match")


def check_graph(d):
    q=1<<d
    S=set(range(1,q))|{i<<d for i in range(1,q)}
    N=q*q
    C=Counter()
    for z in range(1,N):
        x=sum((p^z) in S for p in S)
        val=q-2 if z in S else 2
        assert x==val
        C[x]+=1
    unknown=set(S)
    parsed=[]
    while unknown:
        a=min(unknown)
        part={x for x in S if x==a or x^a in S}
        assert all((x^y) in S for x,y in combinations(part,2))
        assert part<=unknown and len(part)==q-1
        parsed.append(part)
        unknown-=part
    assert len(parsed)==2 and all({x^y for x,y in product(p|{0},repeat=2)}==p|{0} for p in parsed)
    print("independent Cayley",d,"common-neighbor histogram",sorted(C.items()),
          "and exactly two additive cliques")


def main():
    for d in (4,6):
        check_graph(d)
    check_f(gf16_cube())
    f=row11()
    check_f(f)
    if len(sys.argv)>1:
        data=Path(sys.argv[1]).read_bytes()
        assert len(data)==2235 and md5(data).hexdigest()=="f4035110834ac7b87553da3449e66790"
        assert sha256(data).hexdigest()=="74fba5a5b95d16a21bbafe262041a10ba0bec5c0e4120413315d3741fae478fe"
        rows=data.splitlines()
        assert len(rows)==13
        assert [int(s,16) for s in rows[10].split(b",") if s]==f
        print("provenance: all 64 entries equal the authors' QAPN-6-6 row 11")
    print("PASS: independent Cayley, spectra and direct plane parity")


if __name__=="__main__":
    main()
