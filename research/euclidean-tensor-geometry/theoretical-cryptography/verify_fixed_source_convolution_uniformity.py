#!/usr/bin/env python3
"""Finite algebra checks for the known-law support theorem, no external input."""
from collections import Counter
from fractions import Fraction as Fr
from itertools import product
from random import Random

tally=Counter()


class Field:
    def __init__(self,q):
        self.q=q
        self.p=2 if q==4 else q
        self.add=[[self._add(x,y) for y in range(q)] for x in range(q)]
        self.mul=[[self._mul(x,y) for y in range(q)] for x in range(q)]
    def _add(self,x,y):
        return x^y if self.q==4 else (x+y)%self.q
    def _mul(self,x,y):
        if self.q!=4:
            return x*y%self.q
        a=0
        while y:
            if y&1:
                a^=x
            x<<=1
            if x&4:
                x^=7
            y>>=1
        return a
    def summ(self,x):
        a=0
        for b in x:
            a=self.add[a][b]
        return a
    def tr(self,x):
        return x^self.mul[x][x] if self.q==4 else x
    def scale(self,x,v):
        return tuple(self.mul[x][a] for a in v)
    def comb(self,w,V,r):
        return tuple(self.summ(self.mul[a][v[i]] for a,v in zip(w,V)) for i in range(r))
    def dot(self,v,x):
        return self.summ(self.mul[a][b] for a,b in zip(v,x))
    def stabilizer(self,R):
        return {s for s in range(1,self.q) if {self.scale(s,v) for v in R}==R}


def fourier_support(F,r,nu):
    pts=list(product(range(F.q),repeat=r))
    ans=set()
    for v in pts:
        mass=[Fr(0)]*F.p
        for x,m in nu.items():
            mass[F.tr(F.dot(v,x))]+=m
        if any(k!=mass[0] for k in mass):
            ans.add(v)
    return ans


def known_law(F,r,R):
    pts=list(product(range(F.q),repeat=r))
    Z=F.q**r
    nz=R-{(0,)*r}
    nu={}
    for x in pts:
        c=Counter(F.tr(F.dot(v,x)) for v in nz)
        assert all(c[j]==c[1] for j in range(1,F.p))
        nu[x]=Fr(Z+c[0]-c[1], Z*Z)
    assert sum(nu.values())==1 and min(nu.values())>0
    assert R==fourier_support(F,r,nu)
    tally["known positive templates"]+=1
    return nu


def allowed_full(F,r,R,m):
    choices=list(product(sorted(R),repeat=m))
    S=F.stabilizer(R)
    accept=[]
    for w in product(range(F.q),repeat=m):
        if all(F.comb(w,V,r) in R for V in choices):
            accept.append(w)
        tally["coefficient rows"]+=1
    assert set(accept)=={(0,)*m}|{tuple(s if i==j else 0 for i in range(m))
                                 for j in range(m) for s in S}
    return accept


def check_gate(F,B,accept,S):
    m=len(B)
    r=len(B[0])+1
    images=Counter(F.comb(w,[(1,)+b for b in B],r) for w in accept)
    assert images == Counter({(0,)*r:1,**{(s,)+F.scale(s,b):1
                                          for s,b in product(S,B)}})
    tally["zero/active gates"]+=1
    return set(images)


def pin_matrices(F,r,R):
    pts=list(product(range(F.q),repeat=r))
    zero=(0,)*r
    g=next(x for x in pts if x not in R)
    chosen={}
    for v in pts:
        if v==zero:
            continue
        for cols in product(pts,repeat=r):
            if F.comb(v,cols,r)!=g:
                continue
            im={F.comb(w,cols,r) for w in pts}
            if len(im)==len(pts):
                chosen[v]=cols
                break
        assert v in chosen
    assert {x for x in pts if all(F.comb(x,C,r) in R for C in chosen.values())} == {zero}
    tally["invertible pins"]+=len(chosen)
    return chosen


def test_padding(F,r,R,pin):
    pts=list(product(range(F.q),repeat=r))
    q=F.q
    for V in product(pts,repeat=2):
        for x in product(range(q),repeat=2):
            Bx=F.comb(x,V,r)
            im={F.comb((1,1),(Bx,z),r) for z in pts}
            assert len(im)==len(pts)
            sat={z for z in pts if F.comb((1,1),(Bx,z),r) in R
                 and all(F.comb(z,C,r) in R for C in pin.values())}
            assert sat==({(0,)*r} if Bx in R else set())
            tally["padded fibers"]+=1


rng=Random(93241)
for q,r in ((2,2),(3,2),(4,1),(4,2),(5,2)):
    F=Field(q)
    pts=list(product(range(q),repeat=r))
    if (q,r)==(4,1):
        R={(0,),(1,),(2,)}
    else:
        R={x for x in pts if sum(a!=0 for a in x)<=1}
    nu=known_law(F,r,R)
    assert any(F.comb((1,1),(u,v),r) not in R for u,v in product(R,repeat=2))
    S=F.stabilizer(R)
    a2=allowed_full(F,r,R,2)
    allowed_full(F,r,R,3)
    check_gate(F,[(0,),(1,)],a2,S)
    pin=pin_matrices(F,r,R)
    test_padding(F,r,R,pin)
    if q==2:
        a7=allowed_full(F,r,R,7)
    else:
        # Intersect the independent, exactly enumerated two-coordinate
        # conditions at every pair, then compare to finite gate graph.
        a7=[w for w in product(range(q),repeat=7)
            if all((w[i],w[j]) in a2 for j in range(7) for i in range(j))]
    allB=list(product(range(2),repeat=3))
    graphs={bad:check_gate(F,[v for v in allB if v!=bad],a7,S) for bad in allB}
    for _ in range(33):
        cls=[(rng.choice(allB),rng.sample(range(4),3)) for i in range(rng.randrange(1,7))]
        masks=lambda t,x: all((t,)+(tuple(x[i] for i in idx)) in graphs[b] for b,idx in cls)
        n=sum(all(tuple(v[i] for i in idx)!=b for b,idx in cls)
              for v in product(range(2),repeat=4))
        count=sum(masks(s,z) for s in S
                  for z in product((0,s),repeat=4))
        assert count==len(S)*n and masks(0,(0,0,0,0))
        tally["finite formula counts"]+=1

F=Field(4)
nu=known_law(F,1,{(0,),(1,)})
assert fourier_support(F,1,nu)=={(0,),(1,)}
assert {(F.mul[2][x],) for (x,) in fourier_support(F,1,nu)}!={(0,),(1,)}
F=Field(2)
nu=dict(zip(product(range(2),repeat=2),map(lambda x:Fr(x,8),(3,2,2,1))))
assert fourier_support(F,2,nu)=={(0,0),(0,1),(1,0)}

# Compute small entire forward laws in the primal domain independently.
for q,r in ((2,2),(3,2),(4,1)):
    F=Field(q)
    d=3 if q<4 else 2
    pts=list(product(range(q),repeat=r))
    ys=list(product(range(q),repeat=d))
    R={(0,),(1,),(2,)} if q==4 else {
        x for x in pts if sum(a!=0 for a in x)<=1}
    nu=known_law(F,r,R)
    for _ in range(40):
        Ts=[]
        for k in range(rng.randrange(1,6)):
            while True:
                T=rng.choices(pts,k=d)
                if len({F.comb(y,T,r) for y in ys})==len(pts):
                    break
            Ts.append(T)
        w={(0,)*d:Fr(1)}
        for T in Ts:
            nxt=Counter()
            for x,pr in w.items():
                for u,m in nu.items():
                    y=tuple(F.add[x[i]][F.dot(T[i],u)] for i in range(d))
                    nxt[y]+=pr*m
            w=dict(nxt)
        assert sum(w.values())==1
        expect={y for y in ys if all(F.comb(y,T,r) in R for T in Ts)}
        assert expect==fourier_support(F,d,w)
        assert (len(expect)==1)==(len(w)==len(ys) and len(set(w.values()))==1)
        tally["whole forward laws"]+=1

print("PASS exact convolution support dichotomy checks:",dict(tally))
