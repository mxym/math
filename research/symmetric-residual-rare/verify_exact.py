#!/usr/bin/env python3
"""Conditional pad histograms over finite fields, with no floating point."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product


def field(q, polynomial):
    bits = q.bit_length()-1
    def mul(x,y):
        z = 0
        while y:
            if y & 1:
                z ^= x
            x <<= 1
            if x & q:
                x ^= polynomial
            y >>= 1
        assert z < q
        return z
    tables = [[mul(x,y) for y in range(q)] for x in range(q)]
    for x in range(1,q):
        assert set(tables[x]) == set(range(q))
    return bits,tables


def tv_uniform(hist, target, total):
    acc = sum(abs(hist.get(i,0)*target-total) for i in range(target))
    return Q(acc,2*target*total)


def direct_conditions(q, polynomial):
    d, mt = field(q,polynomial)
    size = q**4
    code = []
    for x in range(size):
        u1,u2,v1,v2 = [x >> (i*d) & (q-1) for i in range(4)]
        code.append(mt[u1][v1]^mt[u2][v2])
    selected = list(range(size)) if q<=4 else sorted(
        {0,1,2,q,q*q,q**3,1+q*q,q+q**3,size-1}
    )
    squared_count = odd_count = unconditional_count = 0
    max_joint = Q()
    for z in selected:
        pairs = Counter((code[x],code[x^z]) for x in range(size))
        assert sum(pairs.values()) == size
        arr = {i*q+j:c for (i,j),c in pairs.items()}
        phi = [3,5] if q<=4 else [3,5,7]
        if z:
            chi2 = sum(Q((arr.get(a,0)*q*q-size)**2,q*q*size**2)
                       for a in range(q*q))
            assert chi2 == Q(q*(q-1),q**4)
            t = tv_uniform(arr,q*q,size)
            assert 4*t*t<=chi2 and t<Q(1,2*q)
            max_joint = max(max_joint,t)
            squared_count += 1
            add_f = Counter()
            for (p,r),w in pairs.items():
                add_f[p^r] += w
            assert tv_uniform(add_f,q,size)==0
        else:
            assert all(p==r for p,r in pairs)
        for M in phi:
            push = Counter()
            phi_hist = Counter(x%M for x in range(q))
            assert tv_uniform(phi_hist,M,q)<=Q(M,2*q)
            for (p,r),w in pairs.items():
                push[(p%M+r%M)%M] += w
            t = tv_uniform(push,M,size)
            if z:
                assert t <= Q(1,2*q)+Q(M,q)
                odd_count += 1
            unconditional_count += 1
    # Compare the fully averaged joint (Z, field pad sum) when all Z are used.
    if len(selected)==size:
        etv = sum(tv_uniform(Counter(code[x]^code[x^z] for x in range(size)),
                              q,size) for z in selected)/size
        assert etv == Q(q-1,q**5)
    # A linear pad is a negative control: fixing Z fixes its pad sum.
    linear = lambda x: x & (q-1)
    z = q+1
    collapse = Counter(linear(x)^linear(x^z) for x in range(size))
    assert len(collapse)==1 and tv_uniform(collapse,q,size)==1-Q(1,q)
    print(f'GF({q}): {squared_count} nonzero carrier conditions, '
          f'max joint TV {max_joint}, {odd_count} odd-pad checks, '
          f'{unconditional_count} projections incl. zero')
    return squared_count,odd_count


if __name__=='__main__':
    for q,p in ((2,0b11),(4,0b111),(8,0b1011)):
        direct_conditions(q,p)
    print('negative control: linear pads are deterministic at fixed carrier sum')
    print('PASS exact collision laws, zero atom, and non-power-of-two pad groups')
