#!/usr/bin/env python3
"""Exact Gram and all-pairs ray tests of ten order-nine Schur-product witnesses."""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import sys
from urllib.request import urlopen

URL = ("https://wiki.aalto.fi/download/attachments/120482261/BH-9-6.txt"
       "?api=v2&modificationDate=1499265159731&version=1")
WANT_SHA = "e6b0c65c17700e3d9a5141b5ba74e025cbbde9d39809a25b89c98ef1083ff5a7"
U = range(9)
Z6 = ((2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1))

def mul(u,v,q):
    return (u[0]*v[0]-q*u[1]*v[1], u[0]*v[1]+u[1]*v[0])

def bar(z):
    return (z[0],-z[1])

def inner(u,v,q):
    return tuple(map(sum,zip(*(mul(bar(x),y,q) for x,y in zip(u,v)))))

def load_source():
    if len(sys.argv)==2:
        data=Path(sys.argv[1]).read_bytes()
    else:
        assert len(sys.argv)==1
        with urlopen(URL,timeout=30) as f:
            data=f.read()
    lines=data.decode("ascii").splitlines()
    canonical=("\n".join(lines)+"\n").encode()
    assert len(lines)==17 and len(canonical)==1496 and sha256(canonical).hexdigest()==WANT_SHA
    mats=[]
    for r in lines:
        assert r[:6]=="BH1996" and len(r)==87 and set(r[6:])<=set("012345")
        nums=list(map(int,r[6:]))
        a=tuple(tuple(nums[9*i:9*i+9]) for i in U)
        for i in U:
            for j in range(i,9):
                assert inner([Z6[a[k][i]] for k in U],
                             [Z6[a[k][j]] for k in U],3)==((36,0) if i==j else (0,0))
        mats.append(a)
    return mats

def checker(A,B,s,rev,q,scale,want,modulus):
    assert len(s)==9 and sorted(s)==list(U)
    E={(a,b):tuple(A[k][a]+B[s[k]][b] for k in U)
                 for a,b in product(U,repeat=2)}
    if modulus:
        keys={ij:tuple((x-e[0]) % modulus for x in e) for ij,e in E.items()}
    else:
        assert {sum(e) for e in E.values()}=={0}
        keys=E
    V={(a,b):tuple(mul(rev(A[k][a]),rev(B[s[k]][b]),q) for k in U)
                for a,b in E}
    grams=0
    for axis in (0,1):
        for a in U:
            row=[V[a,b] if axis==0 else V[b,a] for b in U]
            for b in U:
                for c in range(b,9):
                    assert inner(row[b],row[c],q)==((9*scale**4,0) if b==c else (0,0))
                    grams+=1
    assert grams==810
    dephased={}
    for ij,v in V.items():
        assert mul(v[0],bar(v[0]),q)==(scale**4,0)
        dephased[ij]=tuple(mul(x,bar(v[0]),q) for x in v)
    checked=0
    for a,b in combinations(V,2):
        assert (dephased[a]==dephased[b])==(keys[a]==keys[b])
        checked+=1
    counts=Counter(dephased.values())
    assert checked==3240
    if want is not None:
        assert len(counts)==want
    return len(counts), sorted(Counter(counts.values()).items())

M=load_source()
print(f"official BH(9,6): {len(M)} records; canonical 1496-byte SHA256 {WANT_SHA}; all Gram tests PASS")
ws=json.loads(Path(__file__).with_name("witnesses.json").read_text())
assert set(map(int,ws))=={60,62,65,66,68,69,70,71,74}
def get(a):
    i,t=a["i"],a["t"]
    assert 1<=i<=17 and t in (0,1)
    H=M[i-1]
    return tuple(zip(*H)) if t else H
for c,x in sorted(ws.items(),key=lambda t:int(t[0])):
    n,hist=checker(get(x["X"]),get(x["Y"]),x["p"],lambda a:Z6[a],3,2,int(c),6)
    print(f"BH {c}: 810 Gram entries, 3240 pairs, multiplicities {hist}")
x=ws["74"]
n,_=checker(get(x["X"]),get(x["Y"]),list(U),lambda a:Z6[a],3,2,None,6)
assert n<=45
print(f"BH negative control: identity changes 74 to {n}")

def chi(x):
    return 0 if x==0 else 1 if x in (1,2,3,6) else -1
def subt(k,a):
    return ((k%3-a%3)%3)+3*((k//3-a//3)%3)
X=tuple(tuple(chi(subt(k,a)) for a in U) for k in U)
n,hist=checker(X,X,[0,5,7,4,6,2,8,1,3],lambda a:(4,0) if a==0 else (1,a),15,4,73,None)
print(f"three-value 73: 810 Gram entries, 3240 pairs, multiplicities {hist}")
