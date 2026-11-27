"""Exact check of orbit-averaged trace equations and truth-table degrees."""
import math
from functools import reduce
from operator import xor

MOD = {2:7, 3:11, 4:19, 5:37, 6:67, 7:131, 8:285, 9:529, 10:1033}


def req(x, text):
    if not x:
        raise ValueError(text)


def checked_field(n):
    size = 1 << n
    def mul(x, y):
        out = 0
        while y:
            if y & 1:
                out ^= x
            y >>= 1
            x <<= 1
            if x >= size:
                x ^= MOD[n]
        return out
    def power(a, k):
        res = 1
        while k:
            if k & 1:
                res = mul(res,a)
            a = mul(a,a)
            k >>= 1
        return res
    req(all(power(x,size-1)==1 for x in range(1,size)), 'not a field')
    Tr = [reduce(xor,(power(x,1<<j) for j in range(n)),0) for x in range(size)]
    req(set(Tr)=={0,1}, 'trace')
    return mul,power,Tr


def run(n):
    size = 1 << n
    mul,powf,tr=checked_field(n)
    good = []
    for k in range(1,n):
        if math.gcd(n,k)!=1:
            continue
        d=(1<<k)-1
        # S contains exactly the constants whose trace pairing with A is one.
        S={1} | {mul(powf(1^r,d),1^powf(r,size-1-d)) for r in range(2,size)}
        solutions = [a for a in range(size) if all(tr[mul(s,a)] for s in S)]
        req(bool(solutions)==(n-k<=2),'unexpected averaged-system outcome')
        if solutions:
            good.append(k)

        # Enumerate all 2^(2n) values at z=0 and extract ANF by Moebius.
        if n<=6:
            truth = [1^tr[mul(x,powf(y,size-(1<<k)))]
                     for y in range(size) for x in range(size)]
            for j in range(2*n):
                for i in range(len(truth)):
                    if i & (1<<j):
                        truth[i] ^= truth[i^(1<<j)]
            degree=max(i.bit_count() for i,c in enumerate(truth) if c)
            req(degree==n-k+1,'truth-table degree')
    print(f'n={n}: compatible k={good}')


if __name__=='__main__':
    for n in MOD:
        run(n)
