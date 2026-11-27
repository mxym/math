#!/usr/bin/env python3
"""Exact witness geometry, dual-code distance, and direct-block regressions."""
from itertools import product
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

class GF2m:
    def __init__(self, m, modulus):
        self.m,self.modulus,self.Q=m,modulus,1<<m
        self.log,self.exps=[-1]*self.Q,[]
        x=1
        for i in range(self.Q-1):
            assert x and self.log[x]==-1
            self.log[x]=i
            self.exps.append(x)
            x<<=1
            if x&self.Q:
                x^=modulus
        assert x==1 and all(a>=0 for a in self.log[1:])

    def mul(self,x,y):
        return self.exps[(self.log[x]+self.log[y])%(self.Q-1)] if x and y else 0

    def div(self,x,y):
        return self.exps[(self.log[x]-self.log[y])%(self.Q-1)] if x else 0

    def trace(self,x):
        t=0
        for _ in range(self.m):
            t^=x
            x=self.mul(x,x)
        assert t in (0,1)
        return t

def parse():
    src=Path(__file__).with_name("WITNESSES.txt")
    rows=[tuple(map(int,line.split())) for line in src.read_text().splitlines() if line and not line.startswith("#")]
    cases=[]
    while rows:
        m,p=rows.pop(0)
        cols,rows=rows[:m+3],rows[m+3:]
        assert len(cols)==m+3 and all(len(v)==3 and all(0<=a<1<<m for a in v) for v in cols)
        cases.append((m,p,cols))
    assert [m for m,p,c in cases]==[7,9,11]
    return cases

def insert(piv,v):
    while v:
        i=v.bit_length()-1
        if i in piv:
            v^=piv[i]
        else:
            piv[i]=v
            return True
    return False

def rank(vectors):
    piv={}
    for v in vectors:
        insert(piv,v)
    return len(piv)

def point_dictionary(F,cols):
    vectors=[(0,0,0)]
    for a,b,c in cols:
        vectors += [(x^a,y^b,z^c) for x,y,z in vectors]
    projective=set()
    for v in vectors[1:]:
        a=next((a for a in v if a),0)
        if a==0:
            return None
        key=tuple(F.div(x,a) for x in v)
        if key in projective:
            return None
        projective.add(key)
    return vectors,projective

def direct_dual_minimum(F,cols):
    m,Q=F.m,F.Q
    def triple(mask):
        return tuple((mask>>(m*j))&(Q-1) for j in range(3))
    traces=[F.trace(i) for i in range(Q)]
    basis={}
    W=[]
    for mask in range(1,1<<(3*m)):
        v=triple(mask)
        if any(traces[F.mul(a,v[0])^F.mul(b,v[1])^F.mul(c,v[2])] for a,b,c in cols):
            continue
        if insert(basis,mask):
            W.append(v)
        if len(W)==2*m-3:
            break
    assert len(W)==2*m-3
    profile={}
    messages=[(1,a,b) for a,b in product(range(Q),repeat=2)]
    messages.extend((0,1,b) for b in range(Q))
    messages.append((0,0,1))
    for a,b,c in messages:
        r=rank(F.mul(a,x)^F.mul(b,y)^F.mul(c,z) for x,y,z in W)
        profile[r]=profile.get(r,0)+1
    assert profile=={m:Q*Q+Q+1-(1<<(m+3))+1,m-1:(1<<(m+3))-1}
    print(f"m={m}: trace-dual [n,3,d]=[{len(W)},3,{min(profile)}]; profile={sorted(profile.items())}")

def block_check():
    F=GF2m(4,19)
    Q=F.Q
    def pairspace(a):
        return frozenset((0,1,a,1^a))
    spaces={a:pairspace(a) for a in range(2,Q)}
    classes=set()
    regular=irregular=0
    for a,b in product(range(2,Q),repeat=2):
        targets={frozenset(F.mul(x,t) for x in spaces[b]) for t in range(1,Q)}
        equiv=spaces[a] in targets
        if equiv:
            classes.add(tuple(sorted(c for c in range(2,Q)
                                     if spaces[c] in targets)))
        mixed=[]
        for t in range(1,Q):
            if rank((1,a,t,F.mul(t,b)))<=2:
                mixed.append(t)
        assert bool(mixed)==equiv
        if equiv:
            irregular+=1
        else:
            regular+=1
    assert sorted(map(len,classes))==[2,6,6]
    assert (regular,irregular)==(120,76)
    # Same coordinate-value orbit gives an extra rank-two line (lambda=1).
    assert rank((1,2,1,2))==2
    print("GF(16) direct-block negative control: orbit lengths [2, 6, 6], "
          "120 regular ordered pairs with no mixed low-rank line, 76 irregular pairs with one or more")

def main():
    for m,M,cols in parse():
        F=GF2m(m,M)
        _,pg=point_dictionary(F,cols)
        assert len(pg)==(1<<(m+3))-1
        assert point_dictionary(F,cols[:-1]+[cols[0]]) is None
        print(f"q=2 m={m}: {len(pg)} distinct normalized projective points; duplicate-basis negative control rejected")
        if m==7:
            direct_dual_minimum(F,cols)
    block_check()
    print("PASS exhaustive finite witnesses and block regression")

if __name__=="__main__":
    main()
