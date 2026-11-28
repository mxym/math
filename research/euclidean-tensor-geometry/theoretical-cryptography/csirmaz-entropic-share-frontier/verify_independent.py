#!/usr/bin/env python3
"""Combinatorial access structures, symbolic Shannon telescopes, exact 2-D LP."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations
from random import Random


def sum_expr(*terms):
    e=defaultdict(int)
    for f in terms:
        for k,c in f.items():
            e[k]+=c
    return {k:c for k,c in e.items() if c}


def minus(f):
    return {k:-c for k,c in f.items()}


def H(mask):
    return {mask:1}


def cond(U,V):
    return sum_expr(H(U|V),minus(H(V)))


def cmi(U,V,W):
    return sum_expr(H(U|W),H(V|W),minus(H(W)),minus(H(U|V|W)))


def extensions(k):
    left=set(range(1<<k))
    def rec(left,prefix):
        if not left:
            yield tuple(prefix)
        for a in sorted(left):
            if not any(a!=b and a&b==a for b in left):
                yield from rec(left-{a},prefix+[a])
    return rec(left,[])


def order_check(order,k):
    A=(1<<k)-1
    t=A
    idx={m:i for i,m in enumerate(order)}
    weights=[idx[A^(1<<j)] for j in range(k)]
    binary=(sorted(weights)==[1<<j for j in range(k)] and
        all(i==sum(weights[j] for j in range(k) if not D>>j&1) for i,D in enumerate(order)))
    s0=1<<(k+t-1)
    B=[((1<<i)-1)<<k for i in range(t)]
    qual_base=[a|b for a,b in zip(order[:-1],B)]
    def q(M):
        return any(M&x==x for x in qual_base)
    def e(U):
        return cond(s0,U)
    nts=0
    for J in range(1,A+1):
        F=A^J
        pairs=[(j,F|B[i]) for i,j in enumerate(order)
               if j&F==F and j&J]
        P=[p for _,p in pairs]
        D=[d&J for d,_ in pairs]
        Z=[p|J for p in P]
        M=len(P)-1
        assert len(P)==(1<<J.bit_count())-1 and P[0]==F
        assert all(q(z) for z in Z) and not any(q(p) for p in P)
        Ys=[P[j+1]|D[j+1] for j in range(M)]
        Es=[P[j]|D[j+1] for j in range(M)]
        assert all(q(Y) for Y in Ys) and not any(q(E) for E in Es)
        for j,(E,Y) in enumerate(zip(Es,Ys)):
            assert E==Z[j]&Y and Z[j+1]==Z[j]|Y
        for start in range(M+1):
            # Algebraic telescope checked as exact integer identities on
            # independent literal H(S_U) symbols, without entropy numbers.
            lhs=sum_expr(cond(J,P[start]),minus(e(P[-1])),e(Z[start]),
                         *[z for j in range(start,M) for z in (minus(e(Es[j])),e(Ys[j]))])
            rhs=[cond(J,s0|P[-1])]
            for j in range(start,M):
                rhs.append(cmi(Z[j]^Es[j],Ys[j]^Es[j],s0|Es[j]))
                rhs.append(cmi(Es[j]^P[j],P[j+1]^P[j],P[j]))
            assert lhs==sum_expr(*rhs)
            nts+=1
    # Critical equality requires every nonempty subset sum to equal t-index;
    # recover the only possible coordinate weights and check every subset.
    linear=all(sum(weights[j] for j in range(k) if D>>j&1)==t-i
               for i,D in enumerate(order))
    assert binary==linear
    return nts,binary


def vertex_test(a):
    # Full two-dimensional vertex enumeration by all line intersections.
    lines=[(1,0,a),(0,1,a),(1,1,max(3*a,1)),(2,1,1+2*a)]
    verts=set()
    for (i,j,b),(k,l,c) in combinations(lines,2):
        det=i*l-k*j
        if det:
            x,y=(b*l-c*j)/det,(i*c-k*b)/det
            if all(u*x+v*y>=s for u,v,s in lines):
                verts.add((x,y))
    if a<=Q(1,3):
        expected={(a,1),(2*a,1-2*a),(1-a,a)}
    elif a<=Q(1,2):
        expected={(a,1),(1-a,4*a-1),(2*a,a)}
    else:
        expected={(a,2*a),(2*a,a)}
    assert verts==expected,(a,verts,expected)


def main():
    no=nt=nb=0
    for k in (1,2,3,4):
        orders=list(extensions(k)) if k<=3 else []
        if k==4:
            rng=Random(194)
            for _ in range(60):
                subset=list(range(1<<k))
                rng.shuffle(subset)
                subset.sort(key=int.bit_count,reverse=True)
                orders.append(tuple(subset))
            for p in permutations(range(k)):
                orders.append(tuple(sorted(range(1<<k),
                  key=lambda d:sum(1<<p[j] for j in range(k) if not d>>j&1))))
        b=0
        for order in orders:
            n,yes=order_check(order,k)
            nt+=n
            no+=1
            b+=yes
        assert b==len(set(permutations(range(k))))
        nb+=b
    print(f"independent: {no} orders, {nt} symbolic truncated-chain identities, {nb} binary orders PASS")
    params={Q(a,d) for d in range(1,40) for a in range(d+1)}
    for a in params:
        vertex_test(a)
    # Negative control: replay the symmetric candidate forbidden by the i=1 facet.
    a,u,v=Q(1,3),Q(1,3),Q(2,3)
    assert min(u,v)>=a and u+v>=max(3*a,1) and 2*u+v<1+2*a
    print(f"independent: {len(params)} exact polytope vertex checks and asymmetric negative control PASS")


if __name__=="__main__":
    main()
