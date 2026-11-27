#!/usr/bin/env python3
"""Independent binary rank/extension tests and exact cover-lift counts."""
from collections import Counter
from itertools import product


class Binary:
    # Multiply unreduced binary polynomials first, then divide by the
    # monic modulus. The exact-check script reduces differently.
    def __init__(self,n,modulus):
        self.n=n
        self.size=1<<n
        self.modulus=modulus
        self.mul=[[self.multiply(x,y) for y in range(self.size)] for x in range(self.size)]
        self.inv=[None]+[self.mul[x].index(1) for x in range(1,self.size)]

    def multiply(self,x,y):
        word=0
        while y:
            low=y&-y
            word^=x<<(low.bit_length()-1)
            y^=low
        while word.bit_length()>self.n:
            word^=self.modulus<<(word.bit_length()-1-self.n)
        return word

    def frob(self,x,s):
        for _ in range(s):
            x=self.mul[x][x]
        return x


def generate_rank_set(xs):
    space={0}
    for w in xs:
        if w not in space:
            space.update([a^w for a in space])
    assert len(space).bit_count()==1
    return space


def trace_basis(F):
    # The image of x^2+x is the absolute trace kernel. Obtain a basis
    # using binary elimination without evaluating the trace polynomial.
    sq=[F.mul[x][x] for x in range(F.size)]
    pool={v^x for x,v in enumerate(sq)}
    assert len(pool)==F.size//2
    basis=[]
    span={0}
    for x in sorted(pool):
        if x not in span:
            basis.append(x)
            span |= {y^x for y in span}
    assert span==pool and len(basis)==F.n-1
    return basis,pool


def ranks_for_delta(F,basis,delta):
    second=[F.frob(x,1)^F.mul[delta][F.frob(x,F.n-1)] for x in basis]
    # List images of all F-projective linear forms, no slopes evaluated.
    iam=[generate_rank_set(basis)]
    for a in range(F.size):
        row=[w^F.mul[a][x] for x,w in zip(basis,second)]
        iam.append(generate_rank_set(row))
    return second,iam


def extension_count(F,basis,second,iam):
    q=F.size
    generators=[(x<<F.n)|y for x,y in zip(basis,second)]
    U=generate_rank_set(generators)
    assert len(U)==q//2
    expected_rank_size=q//2  # rank m-1 for the extended length m
    assert all(len(v)*2>=expected_rank_size for v in iam)
    # Those original words of rank m-2 need a fresh image value in the
    # new column; all others have sufficient rank already.
    critical=[(a-1,s) for a,s in enumerate(iam) if len(s)<expected_rank_size]
    seen=set(U)
    passed=examined=0
    for v in range(q*q):
        if v in seen:
            continue
        seen.update(x^v for x in U)
        x,y=v>>F.n,v&(q-1)
        if all((x if a==-1 else y^F.mul[a][x]) not in img for a,img in critical):
            passed+=1
        examined+=1
    assert len(seen)==q*q and examined==2*q-1
    return passed,examined


def binary_code_checks():
    tests=extensions=0
    for m,poly,count in [(5,0x29,6),(6,0x61,0),(7,0x89,1),(8,0x11d,0)]:
        F=Binary(m,poly)
        b,_=trace_basis(F)
        good=[]
        for delta in range(1,F.size):
            y,ims=ranks_for_delta(F,b,delta)
            sizes=[len(v) for v in ims]
            assert max(sizes)==F.size//2
            tests+=1
            if min(sizes)>=F.size//4:
                good.append(delta)
                passed,n=extension_count(F,b,y,ims)
                extensions+=n
                assert passed==0
        assert len(good)==count
        if m==7:
            assert good==[1]
        if m in (5,7):
            # Ordinary Frobenius graph: a known extendable positive control.
            y,ims=ranks_for_delta(F,b,0)
            passed,_=extension_count(F,b,y,ims)
            assert passed>=1
    return tests,extensions


def lift_checks():
    targets=0
    for n,poly,basepower in [(5,0x29,1),(7,0x89,1),(8,0x11d,1),(6,0x61,2)]:
        F=Binary(n,poly)
        q=1<<basepower
        AS=[u^F.frob(u,basepower) for u in range(F.size)]
        fibers=Counter(AS)
        assert len(fibers)==F.size//q and set(fibers.values())=={q}
        # Enumerate the pulled-back affine equation in U,V directly.
        lifted=Counter()
        for x,y in product(AS,repeat=2):
            v=F.mul[F.frob(x,basepower)][y]^F.mul[x][F.frob(y,basepower)]
            lifted[v]+=1
        H=set(fibers)
        slopes=Counter()
        for x in H-{0}:
            for y in H-{0}:
                r=F.mul[y][F.inv[x]]
                value=F.mul[F.mul[x][F.frob(x,basepower)]][r^F.frob(r,basepower)]
                slopes[value]+=1
        for target in range(1,F.size):
            assert lifted[target]==q*q*slopes[target]
            targets+=1
        assert sum(lifted.values())==F.size**2
        # Infinity charts: the residue splitter has q simple roots, and
        # the q finite direction ratios are precisely the fixed subfield.
        directions=[v for v in range(F.size) if F.frob(v,basepower)==v]
        assert len(directions)==q and len(directions)+1==q+1
    return targets


if __name__=="__main__":
    tests,extensions=binary_code_checks()
    print(f"independent PASS: {tests} binary code-rank classifications; {extensions} complete extension cosets ruled out")
    print("independent PASS: two extendable Frobenius-graph controls")
    print(f"independent PASS: {lift_checks()} nonzero targets with exact q-square Artin–Schreier affine lift counts")
