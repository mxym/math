#!/usr/bin/env python3
"""Exact cycle-word, relation-classification and marked-edge checks."""
from itertools import permutations, product

checks = 0


def check(ok):
    global checks
    checks += 1
    if not ok:
        raise AssertionError("exact check failed")


def steps(z, a, sign, G):
    return tuple((x+sign*y) % m for x,y,m in zip(z,a,G))


def neighbors(v, S, G):
    i,z = v
    return [(1-i,steps(z,a,1-2*i,G)) for a in S]


def trace(word,S,G):
    z = (0,)*len(G)
    P = [(0,z)]
    for j,c in enumerate(word):
        z = steps(z,S[int(c)],(-1)**j,G)
        P.append(((j+1)%2,z))
    return P


def simple(P):
    return P[0]==P[-1] and len(set(P[:-1]))==len(P)-1


def has_cycle(S,G,n,marked=False):
    v = (0,(0,)*len(G))
    seen = {v}
    def visit(u,left):
        if left==1:
            return v in neighbors(u,S,G)
        for w in neighbors(u,S,G):
            if w not in seen:
                seen.add(w)
                if visit(w,left-1):
                    return True
                seen.remove(w)
        return False
    if marked:
        u = (1,(0,)*len(G))
        seen.add(u)
        return visit(u,n-1)
    return visit(v,n)


def marked_lengths(S,G):
    v = (0,(0,)*len(G))
    u = (1,(0,)*len(G))
    seen = {v,u}
    lengths = set()
    def visit(w):
        for z in neighbors(w,S,G):
            if z==v:
                if len(seen)>=4:
                    lengths.add(len(seen))
            elif z not in seen:
                seen.add(z)
                visit(z)
                seen.remove(z)
    visit(u)
    return lengths


types4 = [(2,-2,0),(2,-1,-1)]
types8 = [(4,-4,0),(4,-3,-1),(4,-2,-2),(3,-3,0),(3,-2,-1)]


def relation(coeffs,S,G):
    return any(all(sum(c*v[i] for c,v in zip(C,T)) % m==0
                   for i,m in enumerate(G))
               for C in coeffs for T in permutations(S))


def lattice_differences(P):
    V = set()
    for i,(p,x) in enumerate(P[:-1]):
        for q,y in P[i+1:-1]:
            if p==q:
                d=tuple(a-b for a,b in zip(x,y))
                V.add(max(d,tuple(-a for a in d)))
    return V


def winding(m,s):
    P = [(0,(0,0))]
    for j in range(m):
        i=(-j)%m
        k=(i-1)%m
        P.append((1,(i,0)))
        if j<s:
            P.extend([(0,(k,1)),(1,(i,1))])
        P.append((0,(k,0)))
    return P


def main():
    base=((0,0),(1,0),(0,1))
    word="0101012010201212"
    # A modulus exceeding twice the prefix displacement lifts residues
    # uniquely to the integer coefficient lattice for these short words.
    L=100
    P=trace(word,base,(L,L))
    check(simple(P))
    F=[(p,tuple((a+L//2)%L-L//2 for a in z)) for p,z in P]
    D=lattice_differences(F)
    check(D=={(0,1),(0,2),(1,-1),(1,-2),(1,0),(1,1),(1,2),
               (2,-1),(2,-2),(2,0),(2,1),(3,-1),(3,0)})

    triples=0
    freqs=[0,0,0]
    for m in range(1,8):
        for n in range(m,9):
            G=(m,n)
            elts=list(product(range(m),range(n)))
            for i,x in enumerate(elts[1:],1):
                for y in elts[i+1:]:
                    S=((0,0),x,y)
                    triples+=1
                    a=has_cycle(S,G,4)
                    check(a==relation(types4,S,G))
                    if a:
                        freqs[0]+=1
                        continue
                    b=has_cycle(S,G,8)
                    check(b==relation(types8,S,G))
                    if b:
                        freqs[1]+=1
                        continue
                    check(simple(trace(word,S,G)))
                    freqs[2]+=1
    check(not has_cycle(base,(5,5),4))
    check(not has_cycle(base,(5,5),8))
    check(simple(trace(word,base,(5,5))))

    for m in range(3,12):
        M=1 << (2*m-1).bit_length()
        S=((0,0),(1,0),(1,1))
        G=(m,2)
        k=4
        while k<M:
            check(not has_cycle(S,G,k,marked=True))
            k*=2
        check(has_cycle(S,G,M,marked=True))
        if m<=7:
            check(marked_lengths(S,G)=={4*r+2 for r in range(1,m)} |
                                         {2*m+2*s for s in range(m+1)})
    for m in range(3,41):
        S=((0,0),(1,0),(1,1))
        for s in range(m+1):
            P=winding(m,s)
            check(len(P)==2*m+2*s+1)
            check(simple(P))
            check(all(v in neighbors(u,S,(m,2)) for u,v in zip(P,P[1:])))
    print(f"Two-orbit cycle checks passed: {checks} exact assertions; "
          f"{triples} triples; shortest power-of-two lengths 4/8/16 "
          f"occurred in {freqs} triples.")


if __name__=="__main__":
    main()
