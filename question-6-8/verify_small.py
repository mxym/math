#!/usr/bin/env python3
"""Exact finite field, permutation, and trace-collision checks for Question 6.8."""
from hashlib import sha256

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

class Field:
    def __init__(self, e, modulus):
        self.e, self.modulus, self.Q = e, modulus, 1 << (2*e)
        Q = self.Q
        self.exp, self.log = [], [-1]*Q
        t=1
        for j in range(Q-1):
            assert t and self.log[t] == -1
            self.exp.append(t)
            self.log[t]=j
            t <<= 1
            if t & Q:
                t ^= modulus
        assert t==1 and all(s>=0 for s in self.log[1:])
        self.trace4 = [self.trace(x,4) for x in range(Q)]
        self.F4 = tuple(x for x in range(Q) if self.power(x,4)==x)
        assert len(self.F4)==len(set(self.trace4))==4

    def power(self, x, j):
        return self.exp[self.log[x]*j%(self.Q-1)] if x else 0

    def mul(self, x, y):
        return self.exp[(self.log[x]+self.log[y])%(self.Q-1)] if x and y else 0

    def trace(self, x, q):
        s = 0
        for j in range(self.e if q==4 else self.e//2):
            s ^= self.power(x,q**j)
        return s

    def g(self, x):
        t,u = self.trace4[x], x^self.power(x,4)
        return self.power(x,32)^self.mul(self.power(t,2),1^self.power(u,9))


small = {
    (6,4179):(10,1180,1278,12),
    (6,8137):(224,58,873,2035),
    (8,65581):(66,26884,34160,37251),
    (8,131053):(330,6202,4686,28143),
}

def main():
    F=Field(3,67)
    assert tuple(F.g(x) for x in F.F4)==(0,)*4
    print("e=3 subfield negative control:", F.F4, "all map to 0")
    for e,m in ((4,285),(4,501),(6,4179),(6,8137),(8,65581),(8,131053)):
        F=Field(e,m)
        Q=F.Q
        tab=[F.g(x) for x in range(Q)]
        img=len(set(tab))
        J=[z for z in range(Q) if F.trace(z,16)==1 and F.trace4[F.power(z,9)]==1]
        assert img=={4:256,6:2476,8:42688}[e] and len(J)=={4:0,6:72,8:1024}[e]
        if e==4:
            assert set(tab)==set(range(256))
            print(f"e=4 modulus={m}: all 256 outputs distinct; LUT SHA256 {sha256(bytes(tab)).hexdigest()}")
        else:
            z,y,w,v=small[e,m]
            assert z==J[0] and z==y^F.power(y,4)
            assert F.trace4[y]==1 and F.trace4[w]==0
            assert tab[y]==tab[w]==v and w==F.power(v,1<<(2*e-5))
            assert y!=w
            print(f"e={e} modulus={m}: image={img}/{Q}, sieve count={len(J)}, "
                  f"(z,y,w,v)=({z},{y},{w},{v}) PASS")
    print("PASS exact full tables and collision certificates")


if __name__ == "__main__":
    main()
