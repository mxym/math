#!/usr/bin/env python3
"""Exact ten-term noncentral 4-cycle kernel and 5-dimensional kernel rank.

No numerical linear algebra, package dependencies, or assertion-only tests.
For all k=0,...,5, verifies that the explicit signed ten-term relation
annihilates EVERY individual image marginal (E,H) in S5. Independently
builds the integer 10x10 edge-image constraints on all 30 four-cycles
of S5 and certifies their exact rational rank 25, giving kernel dimension 5.
The algebraic embedding argument extends this to S_n for every n>=6.
"""
from fractions import Fraction
from itertools import combinations, permutations

# A permutation p=(p[0],...,p[4]) acts on the five labels 0,...,4.
# All ten permutations have cycle type (4,1); precisely five of each sign.
SIGNED_4CYCLES = (
    ((0,3,4,2,1), -1),
    ((0,4,3,1,2),  1),
    ((1,2,3,0,4), -1),
    ((1,3,2,4,0),  1),
    ((2,1,4,0,3),  1),
    ((2,4,1,3,0), -1),
    ((3,0,1,2,4),  1),
    ((3,1,0,4,2), -1),
    ((4,0,2,1,3), -1),
    ((4,2,0,3,1),  1),
)


def insist(condition, reason):
    if not condition:
        raise ArithmeticError(reason)


def cycle_type(p):
    seen=set()
    lengths=[]
    for start in range(len(p)):
        if start in seen:
            continue
        t=start
        length=0
        while t not in seen:
            seen.add(t)
            t=p[t]
            length+=1
        lengths.append(length)
    return tuple(sorted(lengths,reverse=True))


def mapped(p,E):
    return tuple(sorted(p[i] for i in E))


def integer_gaussian_rank(A):
    """Exact row rank over Q; all entries are integers 0/1."""
    if not A:
        return 0
    width=len(A[0])
    rows=[[Fraction(x) for x in row] for row in A]
    height=len(rows)
    r=0
    for col in range(width):
        pivot=next((i for i in range(r,height) if rows[i][col]),None)
        if pivot is None:
            continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        z=rows[r][col]
        rows[r]=[v/z for v in rows[r]]
        for i in range(r+1,height):
            if rows[i][col]:
                w=rows[i][col]
                rows[i]=[a-w*b for a,b in zip(rows[i],rows[r])]
        r+=1
        if r==height:
            break
    return r


def main():
    all_labels=tuple(range(5))
    W=SIGNED_4CYCLES
    insist(len(W)==10 and len({p for p,_ in W})==10,
           "duplicate or missing signed permutations")
    insist(sum(s for _,s in W)==0 and
           [s for _,s in W].count(1)==[s for _,s in W].count(-1)==5,
           "wrong signed masses")
    insist(all(tuple(sorted(p))==all_labels and cycle_type(p)==(4,1)
               for p,_ in W), "support not entirely four-cycles")
    total_constraints=0
    for k in range(6):
        subsets=list(combinations(range(5),k))
        for E in subsets:
            for H in subsets:
                value=sum(sign for p,sign in W if mapped(p,E)==H)
                insist(value==0,f"kernel relation fails at k={k}: {E}->{H}, {value}")
                total_constraints+=1
    insist(total_constraints==252,"incomplete all-rank incidence check")
    print("EXACT TEN-TERM FOUR-CYCLE RELATION: 252 individual marginals vanish.")

    # Restrict to S5's two-subset permutation module, sufficient for all
    # ranks by the proven inclusion-matrix theorem.
    edges=list(combinations(range(5),2))
    class_perms=[p for p in permutations(range(5)) if cycle_type(p)==(4,1)]
    insist(len(class_perms)==30,"wrong four-cycle class size")
    matrix=[[int(mapped(p,E)==H) for p in class_perms]
            for E in edges for H in edges]
    rank=integer_gaussian_rank(matrix)
    insist(rank==25, f"exact rational rank changed: {rank}")
    insist(len(class_perms)-rank==5,"exact rational kernel dimension changed")
    print("EXACT S5 4-CYCLE EDGE-MARGINAL MATRIX: shape 100x30, rank 25.")
    print("EXACT NONCENTRAL ALL-RANK KERNEL DIMENSION: 5.")
    print("NONCENTRAL JOHNSON EQUALITY DIRECTIONS CERTIFIED.")


if __name__=="__main__":
    main()
