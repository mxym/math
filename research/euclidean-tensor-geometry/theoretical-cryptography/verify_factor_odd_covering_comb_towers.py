"""Verify that only the comb/comb pure-tower charts remain at two candidate LCMs."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
from math import prod
import json, sys
if not __debug__:
    raise RuntimeError("Run in normal mode, without -O")
PR=(3,5,7,11,13,17,19,23,29)
CAPS=((4,3,2,2,1,1,1,1,1),(5,3,3,1,1,1,1,1,1))
DEN=100000000

@lru_cache(None)
def kids(s):
    if len(s)==1:
        return tuple()
    assert s[0]=='(' and s[-1]==')'
    out=[];depth=0;mark=1
    for j,ch in enumerate(s[1:-1],1):
        depth+=(ch=='(')-(ch==')')
        if not depth:
            out.append(s[mark:j+1]);mark=j+1
    assert mark==len(s)-1
    return tuple(out)

def node(ss):return '('+''.join(sorted(ss))+')'

@lru_cache(None)
def whole(p,d):
    return node([whole(p,d-1)]*p) if d else '1'

@lru_cache(None)
def after_delete(s,d):
    if s=='0':
        return frozenset()
    if not d:
        return frozenset(['0'])
    ch=kids(s);out=set()
    for i,t in enumerate(ch):
        if i and ch[i-1]==t:
            continue
        for w in after_delete(t,d-1):
            out.add(node(ch[:i]+(w,)+ch[i+1:]))
    return frozenset(out)

def all_shapes(p,d):
    S={whole(p,d)}
    counts=[]
    for e in range(1,d+1):
        S={t for s in S for t in after_delete(s,e)}
        counts.append(len(S))
    return S,counts

def encode(p,d,dead):
    dead=tuple(dead)
    assert sorted(map(len,dead))==list(range(1,d+1))
    assert all(all(ch in '0123456789' and int(ch)<p for ch in s) for s in dead)
    assert not any(u!=v and v.startswith(u) for u in dead for v in dead)
    D=set(dead)
    def read(s):
        if s in D:return '0'
        if len(s)==d:return '1'
        return node(read(s+str(i)) for i in range(p))
    return read('')

def slim_comb(p,d):
    # All parents of the deleted classes lie on a common live spine.
    a=[('0'*(e-1))+str(p-1) for e in range(1,d+1)]
    return encode(p,d,a)

def capacity(s,U,e=0):
    if s=='0':return F(0)
    if s=='1':
        assert e==len(U)
        return U[-1]
    cap=sum(capacity(t,U,e+1) for t in kids(s))
    return min(U[e-1],cap) if e else cap

def exact_loss(cap,first_two,flags,ds):
    L=F(0)
    P={1:F(1)}
    eta=[1,1]+flags
    delta=[F(0),F(0)]+[F(x,DEN) for x in ds]
    assert len(eta)==len(delta)==9 and all(i in (0,1) for i in eta)
    assert all(0<=d<=F(1,2) for d in delta)
    for j,p in enumerate(PR):
        if j<2:
            u=first_two[j]
        else:
            s=sum(F(1,p**e) for e in range(1,cap[j]+1))
            g=1/(1-s) if eta[j] else F(1)
            u=[g*F(1,p**e) for e in range(1,cap[j]+1)]
        c=1/(1-delta[j])
        h=sum(u)
        mx=sum(w*max(F(0), h*(x-eta[j])-delta[j]) for x,w in P.items())
        L+=c*mx
        tails=[F(1)]+[c*x for x in u]+[F(0)]
        assert all(a>=b for a,b in zip(tails,tails[1:]))
        new={}
        for x,w in P.items():
            for k,(a,b) in enumerate(zip(tails,tails[1:]),1):
                if a>b:
                    new[x*k]=new.get(x*k,F(0))+w*(a-b)
        P=new
    return L

def main(data):
    all5,c5=all_shapes(5,3)
    assert c5==[1,1,2]
    for j,cap in enumerate(CAPS):
        all3,c3=all_shapes(3,cap[0])
        assert c3==([1,1,2,6] if j==0 else [1,1,2,6,27])
        comb=(slim_comb(3,cap[0]),slim_comb(5,3))
        exclude=set(product(all3,all5))-{comb}
        seen=set();mx=0
        for row in data:
            if row["profile"]!=j:
                continue
            d3,d5=row["excluded"]
            shape=(encode(3,cap[0],d3),encode(5,3,d5))
            assert shape in exclude and shape not in seen
            seen.add(shape)
            U=[[F(x,DEN) for x in z] for z in row["cap_numerators"]]
            assert len(U)==2
            for s,V,a in zip(shape,U,cap[:2]):
                assert len(V)==a and all(1>=x>=0 for x in V)
                assert all(x>=y for x,y in zip(V,V[1:]))
                assert capacity(s,V)>=1
            assert len(row["flags"])==len(row["delta_numerators"])==7
            v=exact_loss(cap,U,row["flags"],row["delta_numerators"])
            assert v<1
            ppm=-(-v.numerator*1000000//v.denominator)
            mx=max(mx,ppm)
        assert exclude==seen
        print(j,"3-tree counts",c3,"5-tree counts",c5,"excluded",len(seen),"max ppm",mx)
    assert len(data)==64
    print("PASS: precisely the two comb/comb charts remain unexcluded")

if __name__=="__main__":
    if len(sys.argv)!=2:
        raise SystemExit("Usage: python3 VERIFY.py schedule.json")
    main(json.loads(Path(sys.argv[1]).read_text(encoding="utf-8")))
