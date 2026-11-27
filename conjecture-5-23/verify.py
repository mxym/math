#!/usr/bin/env python3
"""Exact field, histogram, and independent finite tuple checks for Conj. 5.23."""
from collections import Counter
from itertools import product
from math import comb, gcd

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")


class Field:
    # Low-to-high coefficients of a monic modulus over F_p.
    def __init__(self, p, mod):
        self.p, self.mod, self.n = p, mod, len(mod)
        self.Q = p**self.n
        self.v = tuple(range(self.Q))
        self.rep = [tuple(x//p**i%p for i in range(self.n)) for x in self.v]
        self.add = [[self.enc((u+v)%p for u,v in zip(a,b))
                     for b in self.rep] for a in self.rep]
        self.mul = [[self.product(a,b) for b in self.rep] for a in self.rep]
        assert all(1 in self.mul[a] for a in self.v[1:])

    def enc(self, a):
        return sum(x*self.p**i for i,x in enumerate(a))

    def product(self, a, b):
        p = self.p
        P = [0]*(2*self.n-1)
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                P[i+j] += u*v
        for i in range(len(P)-1, self.n-1, -1):
            for j, c in enumerate(self.mod):
                P[i-self.n+j] -= c*P[i]
        return self.enc(x % p for x in P[:self.n])

    def power(self, a, k):
        z = 1
        while k:
            if k & 1:
                z = self.mul[z][a]
            a = self.mul[a][a]
            k >>= 1
        return z

    def polynomial(self, terms):
        def value(a):
            z = 0
            for j,b in terms.items():
                z = self.add[z][self.mul[b][self.power(a,j)]]
            return z
        return tuple(value(a) for a in self.v)


def plus(F, x, y):
    z = [0]*F.Q
    for a,u in enumerate(x):
        if u:
            for b,v in enumerate(y):
                z[F.add[a][b]] += u*v
    return tuple(z)


def from_lut(F, h):
    c = Counter(h)
    return tuple(c[b] for b in F.v)


def power_map(F, e, a=1):
    return tuple(F.mul[a][F.power(x,e)] for x in F.v)


def by_tuple(F, maps):
    def value(ys):
        z = 0
        for y in ys:
            z = F.add[z][y]
        return z
    return from_lut(F, (value(ys) for ys in product(*maps)))


def push(cnt, f):
    out = [0]*len(cnt)
    for x, n in enumerate(cnt):
        out[f[x]] += n
    return tuple(out)


def g_formula(p, q, n):
    # Extract g from the defining identity by matching the leading degrees,
    # not from any specialized formula in the conjecture.
    R = {}
    for j in range(q-1, n+1, q-1):
        a = (-comb(n, j)) % p
        if a:
            R[n-j] = a
    G = {}
    while R:
        k=max(R)
        assert k%q == 0
        g = k//q
        b=R[k]
        assert g not in G
        G[g]=b
        for j in range(g+1):
            y = g+(q-1)*j
            v=(R.get(y,0)-b*comb(g,j)*(-1)**(g-j))%p
            if v:
                R[y]=v
            elif y in R:
                del R[y]
    return G


def char_bins(F, count, u):
    # Character with exponent (u dot x) mod p relative to the digit basis.
    c = [0]*F.p
    for x,n in enumerate(count):
        phase = sum(a*b for a,b in zip(F.rep[u],F.rep[x]))%F.p
        c[phase] += n
    return tuple(c)


def main():
    cfg = [(2,(0,)),(3,(0,)),(2,(1,1)),(5,(0,)),(7,(0,)),
           (2,(1,1,0)),(3,(1,0)),(11,(0,)),(2,(1,1,0,0)),
           (5,(2,0)),(3,(1,2,0))]
    pack = {}
    mixed_cases = 0
    for p, mod in cfg:
        F=Field(p,mod)
        Q=F.Q
        C=tuple(range(Q))
        exp = tuple(range(1, 2*Q))
        powers = {r:power_map(F,r) for r in exp}
        # Exhaustive postmaps for the three smallest Q. In larger fields
        # include identity, translation, squaring and constants.
        post = tuple(product(F.v,repeat=Q)) if Q<=4 else (
            F.v,tuple(F.add[1]),powers[2],(1,)*Q)
        # Derive actual g_{n,q} before using it in the same fiber check.
        gs = [(q,n,F.polynomial(g_formula(p,q,n))) for q in (p,p*p)
              for n in range(36)]
        # An extension-field q has an embedded copy in F_Q only if m|e.
        # Check the defining equation directly in each available embedding.
        eqn_cases = 0
        for q,n,g in gs:
            subfield=[a for a in F.v if F.power(a,q)==a]
            if len(subfield)==q:
                for x in F.v:
                    v=0
                    for a in subfield:
                        v=F.add[v][F.power(F.add[x][a],n)]
                    negx=x if p==2 else F.mul[(p-1)][x]
                    assert g[F.add[F.power(x,q)][negx]]==v
                    eqn_cases += 1
        total, brute, yes = 0, 0, 0
        for r,h in powers.items():
            d=gcd(r,Q-1)
            count=(1,)+(0,)*(Q-1)
            fiber=from_lut(F,h)
            for k in range(1,9):
                count=plus(F,count,fiber)
                assert sum(count)==Q**k
                if Q**k<=4096:
                    assert by_tuple(F,[h]*k)==count
                    brute+=1
                for f in (*post,*(g for _,_,g in gs)):
                    N=push(count,f)
                    assert all((N[z]-(z==f[0]))%d==0 for z in C)
                    expected = d==1 and len(set(f))==Q
                    assert (len(set(N))==1)==expected
                    total+=1
                    yes+=expected
                if d>1:
                    assert all(count[b] % d == 0 for b in C[1:])
            if d>1:
                # Exact cyclotomic certificate for every nontrivial
                # additive character. No floating point is involved.
                for u in C[1:]:
                    bins=char_bins(F,fiber,u)
                    assert all((v-(r==0))%d==0 for r,v in enumerate(bins))
                    assert len(set(bins))>1
        # All weighted two-coordinate exponent choices and a deterministic
        # three-coordinate family, with different coefficients and exponents.
        for i,j in product(range(1,Q),repeat=2):
            h1,h2,h3=powers[i],power_map(F,j,2%Q or 1),power_map(F,i+j,Q-1)
            count=plus(F,from_lut(F,h1),from_lut(F,h2))
            assert count==by_tuple(F,[h1,h2])
            assert (len(set(count))==1)==(gcd(i,Q-1)==1 or gcd(j,Q-1)==1)
            M=plus(F,count,from_lut(F,h3))
            assert (len(set(M))==1)==any(gcd(r,Q-1)==1 for r in (i,j,i+j))
            if Q**3<=4096:
                assert by_tuple(F,[h1,h2,h3])==M
            mixed_cases+=2
        pack[Q]=(total,brute,yes,eqn_cases)
        print(f"Q={Q}: {total} composition cases ({yes} balanced), "
              f"{brute} direct tuple comparisons, {eqn_cases} defining-identity values PASS")
    F=Field(3,(0,))
    c=by_tuple(F,[power_map(F,2)]*3)
    assert c==(9,6,12)
    print("negative control: Q=3, ell=2, k=3, counts=(9,6,12); zero fiber alone passes")
    F=Field(7,(0,))
    c=by_tuple(F,[power_map(F,2),power_map(F,3)])
    assert len(set(c))>1 and gcd(gcd(2,6),gcd(3,6))==1
    print(f"mixed-index control Q=7, exponents 2 and 3: counts={c}, common divisor 1 but not balanced")
    print(f"total mixed-index cases: {mixed_cases}; all checks PASS")


if __name__ == "__main__":
    main()
