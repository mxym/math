#!/usr/bin/env python3
"""Exact exhaustive checks of the local/product reduction and refresh law."""

from fractions import Fraction as F
from itertools import product
from collections import Counter


def delta(h, size, add, mul):
    n, m = len(h), len(h[0])
    result = m + 1
    for x in product(range(size), repeat=n):
        if not any(x):
            continue
        w = 0
        for j in range(m):
            t = 0
            for i in range(n):
                t = add(t, mul(x[i], h[i][j]))
            w += t != 0
        result = min(result,w)
        if result == 0:
            break
    return result


def residue_prime(h, p):
    return delta([[v%p for v in row] for row in h],p,
                 lambda x,y: (x+y)%p,lambda x,y: x*y%p)


def exhibit_ring_reduction():
    checked = 0
    for k, primes in ((4,(2,)),(6,(2,3)),(8,(2,)),(9,(3,))):
        for a,b,c,d in product(range(k), repeat=4):
            h=((a,b),(c,d))
            assert delta(h,k,lambda x,y:(x+y)%k,lambda x,y:x*y%k) == min(
                residue_prime(h,p) for p in primes)
            checked += 1

    # The local non-chain ring F2[u,v]/(u^2,uv,v^2) with 3-bit data.
    def square_zero_mul(x,y):
        return (x&1)*(y&1) ^ ((x&1)*(y&6)) ^ ((y&1)*(x&6))

    local = 0
    for a,b,c,d in product(range(8), repeat=4):
        h=((a,b),(c,d))
        assert delta(h,8,lambda x,y:x^y,square_zero_mul)==residue_prime(h,2)
        local += 1

    # A field residue of size four: F4[e]/e^2, e represented in high two bits.
    def f4mul(x,y):
        z = (x if y&1 else 0) ^ ((x<<1) if y&2 else 0)
        return z^7 if z&4 else z

    def f4dual(x,y):
        a,b=x&3,x>>2
        c,d=y&3,y>>2
        return f4mul(a,c) ^ ((f4mul(a,d)^f4mul(b,c))<<2)

    # Test all two-coordinate, one-row generators, including every socle stratum.
    four=0
    for a,b in product(range(16),repeat=2):
        h=((a,b),)
        hbar=((a&3,b&3),)
        assert delta(h,16,lambda x,y:x^y,f4dual)==delta(
            hbar,4,lambda x,y:x^y,f4mul)
        four+=1

    print(f"exact generator margins: {checked} Z/k matrices, "
          f"{local} non-chain local matrices, {four} F4-residue matrices")

    h=((2,0,0),(0,1,1))
    assert delta(h,4,lambda x,y:(x+y)%4,lambda x,y:x*y%4)==0
    assert delta(h,2,lambda x,y:(x+y)%2,lambda x,y:x*y%2)==0
    def image_distance(modulus):
        words = [tuple((a*h[0][j]+b*h[1][j])%modulus for j in range(3))
                 for a,b in product(range(modulus),repeat=2)]
        return min(sum(bool(v) for v in y) for y in words if any(y))
    assert image_distance(4)==1 and image_distance(2)==2
    print("negative control: ordinary image distance without injectivity differs (1 vs 2)")


def proj_distribution(Q,q,p):
    out=[F(0)]*q
    for a in range(Q):
        out[a%q] += 1-p if a==0 else p/(Q-1)
    return out


def convolution(a,b):
    q=len(a)
    return [sum(a[k]*b[(i-k)%q] for k in range(q)) for i in range(q)]


def bernoulli_refresh_tests():
    columns=walks=0
    for Q,q in ((2,2),(3,3),(4,2),(6,2),(6,3),(8,2),(9,3),(25,5)):
        for p in (F(1,19),F(3,19),F(2,7),F(1,2)):
            a=p*Q/(Q-1)
            coeff=proj_distribution(Q,q,p)
            assert coeff==[1-a+a/q]+[a/q]*(q-1)
            for r in range(1,5):
                acc=[F(1)]+[F(0)]*(q-1)
                for j in range(1,r+1):
                    nonzero_x=1+j%(q-1)
                    factor=[coeff[(i*pow(nonzero_x,-1,q))%q] for i in range(q)]
                    acc=convolution(acc,factor)
                u=1-(1-a)**r
                assert acc==[1-u+u/q]+[u/q]*(q-1)
                columns+=1
                # Full q-state distribution against 2-state distribution,
                # all output-weight probabilities, rather than only its mean.
                for length in range(1,8):
                    full={(0,0):F(1)}
                    states={(0,0):F(1)}
                    for _ in range(length):
                        nxt=Counter()
                        for (x,w),mass in full.items():
                            for y,weight in enumerate(acc):
                                xp=(x+y)%q
                                nxt[xp,w+bool(xp)]+=mass*weight
                        full=nxt
                        nxt=Counter()
                        for (st,w),mass in states.items():
                            for to,pi in enumerate((F(1,q),F(q-1,q))):
                                nxt[to,w+to]+=mass*((1-u)*(st==to)+u*pi)
                        states=nxt
                    lumped=Counter()
                    for (x,w),m in full.items():
                        lumped[bool(x),w]+=m
                    assert lumped==states and sum(states.values())==1
                    walks+=1
    print(f"exact refresh law: {columns} projected increment laws; {walks} q-state vs two-state weight laws")
    print("PASS exact commutative-ring reduction and refresh")


if __name__=="__main__":
    exhibit_ring_reduction()
    bernoulli_refresh_tests()
