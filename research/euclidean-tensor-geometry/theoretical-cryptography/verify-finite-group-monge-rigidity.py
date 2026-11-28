#!/usr/bin/env python3
"""Finite checks of convolution-cost ordering rigidity (no inference solver)."""
from fractions import Fraction
from itertools import combinations, permutations, product
from random import Random


class Group:
    def __init__(self,n,mul):
        self.n=n
        self.ids=range(n)
        self.mul=[[mul(a,b) for b in self.ids] for a in self.ids]
        self.inv=[self.mul[a].index(0) for a in self.ids]
        assert all(self.mul[self.inv[a]][a]==0 for a in self.ids)
        self.diff=[[self.mul[self.inv[a]][b] for b in self.ids] for a in self.ids]
        self.chars=tuple(c for tail in product((1,-1),repeat=n-1)
                         for c in [(1,)+tail]
                         if not all(x==1 for x in c)
                         and all(c[self.mul[a][b]]==c[a]*c[b]
                                 for a,b in product(self.ids,repeat=2)))

    def table(self, f):
        return [[f[j] for j in row] for row in self.diff]


def cyclic(n):
    return Group(n,lambda a,b:(a+b)%n)


def klein():
    return Group(4,lambda a,b:a^b)


def dihedral(m):
    def mul(a,b):
        x,j=divmod(a,2)
        y,k=divmod(b,2)
        return 2*((x+(y if j==0 else -y))%m)+(j^k)
    return Group(2*m,mul)


def best_approx(G,f):
    best=((max(f)-min(f))/Fraction(2),(max(f)+min(f))/Fraction(2),0,None)
    for c in G.chars:
        lo=[f[i] for i in G.ids if c[i]<0]
        hi=[f[i] for i in G.ids if c[i]>0]
        mlo=(min(lo)+max(lo))/Fraction(2)
        mhi=(min(hi)+max(hi))/Fraction(2)
        err=max(max(lo)-min(lo),max(hi)-min(hi))/Fraction(2)
        if err<best[0]:
            best=(err,(mlo+mhi)/2,(mhi-mlo)/2,c)
    delta,offset,weight,char=best
    assert delta==max(abs(f[i]-offset-weight*(char[i] if char else 0)) for i in G.ids)
    return best


def defect(T,A,B):
    res=0
    for u,v in A:
        for x,y in B:
            res=max(res,T[u][x]+T[v][y]-T[u][y]-T[v][x])
    return res


def all_exact_checks():
    cases=0
    for G in (cyclic(2),cyclic(3),cyclic(4),klein()):
        pairs=[tuple(combinations(order,2)) for order in permutations(G.ids)]
        for f in product(range(-1,2),repeat=G.n):
            T=G.table(f)
            true=min(defect(T,A,B) for A,B in product(pairs,repeat=2))
            d=best_approx(G,f)[0]
            assert (true==0)==(d==0)
            assert d<=(16 if G.chars else 2)*true
            assert true<=4*d
            cases+=1
    return cases


def sorted_checks(rng):
    trials=0
    for n in range(2,33):
        for _ in range(125):
            vals=[rng.randrange(30) for i in range(n)]
            up=sorted(vals)
            e=max([0]+[x-y for x,y in combinations(vals,2)])
            assert max(abs(x-y) for x,y in zip(vals,up))<=e
            trials+=1
    return trials


def rigid_orbit_checks(rng):
    trials=0
    for G in (cyclic(5),cyclic(6),cyclic(7),cyclic(8),klein(),dihedral(3),dihedral(4)):
        for i in range(75):
            if G.chars:
                c=rng.choice(G.chars)
                scale=rng.randrange(-200,201)
                f=[scale*c[x]+rng.randrange(-2,3) for x in G.ids]
                A=sorted(G.ids,key=lambda x:c[x])
                B=sorted(G.ids,key=lambda x:c[x],reverse=scale>0)
                if i%7==0:
                    rng.shuffle(B)
            else:
                A=list(G.ids)
                B=list(G.ids)
                rng.shuffle(A)
                rng.shuffle(B)
                f=[rng.randrange(-100,101) for x in G.ids]
            e=defect(G.table(f),tuple(combinations(A,2)),tuple(combinations(B,2)))
            assert best_approx(G,f)[0]<=(16 if G.chars else 2)*e
            for t in G.ids:
                g=tuple(f[G.mul[t][x]]-f[x] for x in G.ids)
                gs=[tuple(g[G.mul[G.inv[a]][x]] for x in G.ids) for a in G.ids]
                if max(g)-min(g)>4*e:
                    H={a for a,h in enumerate(gs)
                       if max(abs(u-v) for u,v in zip(g,h))<=2*e}
                    assert len(H)*2==G.n
                    cH=tuple(1 if x in H else -1 for x in G.ids)
                    assert cH in G.chars
                    C=tuple(sum(Fraction(g[G.mul[G.inv[a]][x]],len(H)) for a in H)
                            for x in G.ids)
                    assert C==tuple(C[0]*x for x in cH)
                    assert max(abs(a-b) for a,b in zip(g,C))<=2*e
                trials+=1
    return trials


def compatible(E):
    active=[(a,b,w,c) for a,b,w,c in E if w!=0]
    verts=sorted({v for a,b,*_ in E for v in (a,b)})
    choices=[{c for a,b,w,c in active if v==a or v==b} for v in verts]
    return (all(len(C)<2 for C in choices) and
            any(all(w*s[a]*s[b]<0 for a,b,w,_ in active)
                for s in product((-1,1),repeat=len(verts))))


def triangle_checks():
    G=klein()
    O=[tuple(combinations(order,2)) for order in permutations(G.ids)]
    types=[(0,None)]+[(w,c) for w,c in product((-1,1),G.chars)]
    maps=[]
    for w,c in types:
        T=G.table([w*c[x] if c is not None else 0 for x in G.ids])
        maps.append([sum(1<<j for j,B in enumerate(O) if defect(T,A,B)==0) for A in O])
    trials=0
    for i,j,k in product(range(len(types)),repeat=3):
        E=[(a,b,*types[idx]) for (a,b),idx in zip(((0,1),(0,2),(1,2)),(i,j,k))]
        actual=any(maps[i][a]>>b&1 and maps[j][a]&maps[k][b]
                   for a,b in product(range(len(O)),repeat=2))
        assert actual==compatible(E)
        trials+=1
    return trials


def approximate_checks(rng):
    trials=0
    G=klein()
    pairs=((0,1),(1,2),(2,3),(0,2),(0,3),(1,3))
    kept=weak=0
    for i in range(180):
        signs=tuple(rng.choice((-1,1)) for j in range(4))
        c=rng.choice(G.chars)
        orders=[tuple(combinations(sorted(G.ids,key=lambda x:sg*c[x]),2))
                for sg in signs]
        fs=[]
        for a,b in pairs:
            large=rng.randrange(3)!=0
            w=-(700 if large else 0)*signs[a]*signs[b]
            fs.append([w*c[x]+rng.randrange(-3,4) for x in G.ids])
        e=max(defect(G.table(f),orders[a],orders[b]) for (a,b),f in zip(pairs,fs))
        E=[]
        for (a,b),f in zip(pairs,fs):
            d,off,w,ct=best_approx(G,f)
            assert d<=16*e
            if abs(w)<=17*e:
                w=0
                weak+=1
            else:
                kept+=1
            t=[off+(w*ct[x] if w else 0) for x in G.ids]
            assert max(abs(a-b) for a,b in zip(f,t))<=33*e
            assert defect(G.table(t),orders[a],orders[b])==0
            E.append((a,b,w,ct))
        assert compatible(E)
        trials+=1
    assert weak and kept
    return trials,kept,weak


def main():
    R=Random(291779)
    print("PASS exact tables / sorting / translation orbits / graphs / stability:",
          all_exact_checks(),sorted_checks(R),rigid_orbit_checks(R),
          triangle_checks(),*approximate_checks(R))


if __name__=="__main__":
    main()
