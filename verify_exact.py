#!/usr/bin/env python3
"""Exact field, PGL-orbit, and full auxiliary-reconstruction spot checks."""
from itertools import product, permutations

if not __debug__:
    raise RuntimeError("enable Python assertions")

class BinaryField:
    def __init__(self,m,p):
        self.n=1<<m
        self.logs=[None]*self.n
        self.exps=[]
        x=1
        for i in range(self.n-1):
            assert self.logs[x] is None
            self.logs[x]=i
            self.exps.append(x)
            x<<=1
            if x & self.n:
                x^=p
        assert x==1 and all(v is not None for v in self.logs[1:])
        self.exps*=2
    def mul(self,a,b):
        return self.exps[self.logs[a]+self.logs[b]] if a and b else 0
    def div(self,a,b):
        assert b
        return self.exps[self.logs[a]+self.n-1-self.logs[b]] if a else 0

def vadd(a,b): return (a[0]^b[0],a[1]^b[1])

orbit_count=membership=distinct=matched=translated=0
for m,p in [(2,0x409),(3,0x8003)]:
    q=1<<m
    E=BinaryField(5*m,p)
    F=sorted([0]+[E.exps[i*(E.n-1)//(q-1)] for i in range(q-1)])
    fset=set(F)
    assert len(F)==q
    for a,b in product(F,repeat=2):
        assert a^b in fset and E.mul(a,b) in fset
    matrices=[(a,b,c,d) for a,b,c,d in product(F,repeat=4)
              if (E.mul(a,d)^E.mul(b,c)) and next(x for x in [a,b,c,d] if x)==1]
    assert len(matrices)==q*(q*q-1)
    tags={}
    reps=[]
    for z in range(E.n):
        if z in fset or z in tags: continue
        k=len(reps);reps.append(z)
        for a,b,c,d in matrices:
            w=E.div(E.mul(a,z)^b,E.mul(c,z)^d)
            assert w not in tags and w not in fset
            tags[w]=k
            membership+=1
    assert len(tags)==q**5-q and len(reps)==q*q+1
    orbit_count+=len(reps)
    pairs=list(product(F,repeat=2))
    slopes={a^E.mul(reps[0],b):i for i,(a,b) in enumerate(pairs)}
    assert len(slopes)==q*q
    js=list(permutations(F,3))
    squares={a:E.mul(a,a) for a in F}
    def decoder(P):
        if len(set(P))==1:
            return None
        if len(set(P))==2:
            u,v=sorted(set(P))
            dx,dy=vadd(u,v)
            return slopes.get(E.div(dy,dx)) if dx else None
        a,b=vadd(P[1],P[0]),vadd(P[2],P[0])
        j=0 if a[0] else 1
        r=E.div(b[j],a[j])
        if not all(E.mul(r,x)==y for x,y in zip(a,b)):
            return None
        k=tags.get(r,q*q)
        return k if k<q*q else None

    for s,(z,(a,b)) in enumerate(zip(reps,pairs)):
        slope=a^E.mul(reps[0],b)
        x={t:t^E.mul(z,squares[t]) for t in F}
        assert len(set(x.values()))==q
        for I in js:
            # True distinct branch, including one zero denominator-coordinate.
            P=[(0,x[t]) for t in I]
            assert decoder(P)==s
            distinct+=1
            if m==2:
                P=[vadd((E.mul(x[t],2),E.mul(x[t],3)),(1,z)) for t in I]
                assert decoder(P)==s
                translated+=1
        for a in F[1:]:
            tmap={t:min(t,t^a) for t in F}
            assert all(tmap[t]==tmap[t^a] for t in F)
            points={t:vadd((E.mul(2,x[tmap[t]]),E.mul(E.mul(2,slope),x[tmap[t]])),(1,z)) for t in F}
            for I in js:
                P=[points[t] for t in I]
                assert decoder(P)==s
                matched+=1
    assert decoder([(0,0)]*3) is None
    assert decoder([(0,0),(1,0),(0,1)]) is None
    assert decoder([(0,0),(0,0),(0,1)]) is None
print(f"PGL partitions: {orbit_count} orbits; {membership} exact memberships")
print(f"auxiliary decodes: {distinct} distinct, {matched} matching, {translated} translated nonmatching; all-equal, off-line, and untagged-line negative controls PASS")
print("verify_exact: PASS")
