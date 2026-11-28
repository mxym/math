#!/usr/bin/env python3
"""Independent enumeration in quadratic fields: literal 3-column minors."""
from itertools import combinations, product
from math import comb


class Quadratic:
    def __init__(self, p):
        self.p = p
        self.s = next(x for x in range(2, p) if pow(x, (p-1)//2, p) == p-1)
        self.one = (1, 0)

    def mul(self, x, y):
        a, b = x
        c, d = y
        return ((a*c+self.s*b*d) % self.p, (a*d+b*c) % self.p)

    def power(self, x, k):
        y = self.one
        while k:
            if k % 2:
                y = self.mul(x, y)
            x, k = self.mul(x, x), k//2
        return y

    def nonzero(self):
        return (xy for xy in product(range(self.p), repeat=2) if xy != (0, 0))

    def add(self, x, t):
        return ((x[0]+t) % self.p, x[1])

    def inv(self, x):
        a, b = x
        r = pow((a*a-self.s*b*b) % self.p, -1, self.p)
        return ((r*a) % self.p, (-r*b) % self.p)

    def primitive_root_list(self, n):
        assert (self.p**2-1) % n == 0
        for g in self.nonzero():
            z = self.power(g, (self.p**2-1)//n)
            zz, seq = self.one, []
            for _ in range(n):
                seq.append(zz)
                zz = self.mul(z, zz)
                if zz == self.one:
                    break
            if len(seq) == n:
                assert zz == self.one and len(set(seq)) == n
                return seq
        raise AssertionError("no primitive root")


def count_direct(field, roots):
    p = field.p
    n = len(roots)
    # Generator columns (1,Re(z),Im(z)), not divided differences.
    # They are equivalent over the quadratic splitting field to
    # (1,z,z^q) because q has odd exponent over p in our tests.
    zeros = sum(((b[0]-a[0])*(c[1]-a[1]) -
                 (c[0]-a[0])*(b[1]-a[1])) % p == 0
                for a, b, c in combinations(roots, 3))
    assert zeros <= comb(n, 3)
    return zeros


def curve_points_literal(field, m, h, gamma0):
    # Only used for q=p. Enumerates y^h and x^h via explicit field
    # multiplication. This checks more than the gcd or the minor count.
    U = [z for z in field.nonzero() if field.power(z, field.p+1) == field.one]
    assert len(U) == field.p+1
    powers = [(z, field.power(z, h)) for z in U]
    image = {}
    for _, w in powers:
        image[w] = image.get(w, 0)+1
    assert set(image.values()) == {h}
    rho_target = field.mul(((field.p-1), 0), field.mul(gamma0, gamma0))
    rho = next(z for z, zh in powers if zh == rho_target)
    pts, exceptional = {}, set()
    for x, xh in powers:
        z = field.mul(gamma0, xh)
        assert field.power(z, m) == (field.p-1, 0)
        beta = field.mul(field.mul(z, field.add(z, -1)), field.inv(field.add(z, 1)))
        for y, yh in powers:
            if yh == beta:
                pts[x, y] = z
                if beta == field.one:
                    exceptional.add((x, y))
    for x, y in pts:
        image_x = field.mul((field.p-1, 0), x)
        image_y = field.mul(rho, field.mul(field.mul(x, x), field.inv(y)))
        assert (image_x, image_y) in pts and image_x != x
        back_x = field.mul((field.p-1, 0), image_x)
        back_y = field.mul(rho, field.mul(field.mul(image_x, image_x),
                                        field.inv(image_y)))
        assert (back_x, back_y) == (x, y)
        if (x, y) in exceptional:
            assert (image_x, image_y) not in exceptional
    assert len(pts) % (h*h) == len(exceptional) % (h*h) == 0
    return len(pts), len(exceptional)


def main():
    # Includes h=1, all surviving h=3 pairs, two finite-field
    # extensions, a known h=5 positive, and two q beyond h=3 cutoff.
    cases = [(3,3,8), (11,11,8), (23,23,16), (27,3,8),
             (47,47,32), (59,59,40), (59,59,24), (71,71,48),
             (83,83,56), (343,7,16)]
    check_values = [8,0,0,8,128,200,0,192,224,64]
    point_values = [(4,2),(0,0),(0,0),None,(72,0),(108,18),(0,0),
                    (72,0),(72,0),None]
    print("Direct report (q,n,tested minors,singular minors,curve points,"
          " beta=1 lifts):")
    total = 0
    for (q,p,n), want, want_pts in zip(cases, check_values, point_values):
        m = n//2
        assert m % 4 == 0 and q % n == m-1
        a, exp = q, 0
        while a % p == 0:
            a, exp = a//p, exp+1
        assert a == 1 and exp % 2
        field = Quadratic(p)
        roots = field.primitive_root_list(n)
        for z in roots:
            assert field.power(z, q) == (z[0], -z[1] % p)
        zeros = count_direct(field, roots)
        assert zeros == want, (q,n,zeros)
        total += comb(n, 3)
        if p == q:
            h = (q+1)//m
            pts = curve_points_literal(field, m, h, roots[1])
            assert pts == want_pts, (q,n,pts)
            assert zeros == m*(pts[0]-pts[1])//(h*h)
        else:
            pts = (None, None)
        print((q,n,comb(n,3),zeros,*pts))
    print(f"{total} literal column triples across {len(cases)} codes: PASS.")


if __name__ == "__main__":
    main()
