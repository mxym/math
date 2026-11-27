#!/usr/bin/env python3
"""Finite exact replay of the small exceptional dimensions and trace sieve."""
from hashlib import sha256
from math import isqrt

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

class Field:
    def __init__(self, e, m):
        self.e, self.m, self.Q = e, m, 1 << (2*e)
        Q = self.Q
        self.E, self.L = [], [-1]*Q
        x = 1
        for i in range(Q-1):
            assert x and self.L[x] == -1
            self.E.append(x)
            self.L[x] = i
            x <<= 1
            if x & Q:
                x ^= m
        assert x == 1 and all(v >= 0 for v in self.L[1:])
        self.T = [self.trace(x) for x in range(Q)]
        assert len(set(self.T)) == 4

    def power(self, x, n):
        return self.E[self.L[x]*n%(self.Q-1)] if x else 0

    def mul(self, x, y):
        return self.E[(self.L[x]+self.L[y])%(self.Q-1)] if x and y else 0

    def trace(self, x):
        t = 0
        for i in range(self.e):
            t ^= self.power(x, 4**i)
        return t

    def h(self, x):
        return self.power(x,8)^self.power(x,5)^self.mul(x,self.T[x])

    def trace_conditions(self, b):
        P = self.power
        return self.T[P(b,9)^P(b,6)], self.T[P(b,13)^P(b,10)^P(b,7)]


def first_collision(table, inputs):
    S = {}
    for x in inputs:
        y = table[x]
        if y in S:
            return S[y], x, y
        S[y] = x
    return None


def main():
    for e, m in ((3,67),(3,115),(5,1033),(5,2041),(7,16427),(7,32743)):
        F = Field(e,m)
        Q = F.Q
        table = [F.h(x) for x in range(Q)]
        N = len(set(table))
        assert N == {3:64, 5:619, 7:10147}[e]
        if e == 3:
            assert N == Q
            assert table == [F.power(x,8)^F.power(x,2)^F.power(x,17) for x in range(Q)]
            print(f"e=3 modulus={m}: all 64 values bijective; LUT SHA256 {sha256(bytes(table)).hexdigest()}")
            neg = [F.power(x,8)^F.power(x,5) for x in range(Q)]
            assert neg[0] == neg[1] and len(set(neg))<Q
            continue
        w = first_collision(table,range(Q))
        assert w is not None
        x,y,v = w
        assert x != y and table[x] == table[y] == v
        print(f"e={e} modulus={m}: image={N}/{Q}; collision {x},{y}->{v}; traces {F.T[x]},{F.T[y]}")
        if e == 5:
            assert F.T[x] != F.T[y]
            assert first_collision(table,(x for x in range(Q) if not F.T[x])) is None
            same = first_collision(table,(x for x in range(Q) if F.T[x]==1))
            assert same is not None
            x,y,v = same
            a=x^y
            z=F.mul(x,F.power(a,Q-2))
            b=next(b for b in range(Q) if F.power(b,4)^b==a)
            rhs=F.power(a,3)^1^F.power(a,Q-5)  # extra a^(-4) for trace 1
            assert F.power(z,4)^z==rhs and F.mul(a,z)==x
            assert F.T[x]==F.T[y]==1 and F.T[a]==0
            assert F.power(b,4)^b==a and a and a^x==y
            assert table[x]==table[y]==v
            assert (b,a,z,x,y,v)=={1033:(98,42,653,66,104,593),
                                   2041:(104,133,326,59,190,927)}[m]
            print(f"e=5 modulus={m}: trace-1 b={b}, a={a}, z={z}, collision {x},{y}->{v}")
        if e == 7:
            b = next(b for b in range(Q) if F.trace_conditions(b)==(1,0))
            a = F.power(b,4)^b
            z = next(z for z in range(Q) if F.power(z,4)^z==F.power(a,3)^1)
            h0,h1 = F.mul(a,z),F.mul(a,z)^a
            assert a and h0 != h1 and F.T[h0] == F.T[h1] == 0
            assert table[h0] == table[h1]
            assert (b,a,z,h0,h1,table[h0])=={
                16427:(34,2802,5678,10007,11749,8993),
                32743:(76,15531,4840,15728,475,214)}[m]
            print(f"e=7 modulus={m}: trace-sieve b={b}, a={a}, z={z}, "
                  f"zero-trace collision {h0},{h1}->{table[h0]}")
    F = Field(9,262183)
    J = tuple(b for b in range(F.Q) if F.trace_conditions(b)==(1,0))
    bound = (F.Q-168*isqrt(F.Q))//16
    assert len(J)>=bound>0
    print(f"e=9 trace-sieve exact count={len(J)}; Weil lower bound={bound}")
    print("negative control: omitting y*Tr(y) creates an e=3 collision at 0,1")
    print("PASS exact finite exception and trace-sieve checks")


if __name__ == "__main__":
    main()
