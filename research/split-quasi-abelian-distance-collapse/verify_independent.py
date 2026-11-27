"""Direct exhaustive constituent spaces and independent convolution in GF(4)."""
from itertools import product
from collections import Counter


def ternary_code_census():
    # Four frequency constituents in the two-dimensional ternary space.
    # Generate all words directly as combinations of character rows, not by
    # reconstructing a signed cube or multiplying field-indexed spectra.
    projective_lines = ((1, 0), (0, 1), (1, 1), (1, 2))
    N = 4
    H = tuple(tuple(1 if (x & y).bit_count() % 2 == 0 else 2
                    for y in range(N)) for x in range(N))
    assert all(sum(H[i][k]*H[j][k] for k in range(N)) % 3 == (i == j)
               for i in range(N) for j in range(N))
    vectors = tuple(product(range(3), repeat=N))[1:]
    histogram = Counter()
    for lines in product(projective_lines, repeat=N):
        lo = 2*N
        for sc in vectors:
            c = tuple(sum(a*H[i][j]*lines[i][b] for i, a in enumerate(sc)) % 3
                      for b in range(2) for j in range(N))
            assert any(c)
            # Translation by y acts as scalar H[i][y] on each generator.
            for y in (1, 2):
                shifted = tuple(sum(sc[i]*H[i][y]*H[i][j]*lines[i][b]
                                    for i in range(N)) % 3
                                for b in range(2) for j in range(N))
                assert shifted == tuple(c[b*N+(j^y)] for b in range(2) for j in range(N))
            lo = min(lo, sum(map(bool, c)))
        maxcount = max(Counter(lines).values())
        # A repeated vector occurs on a 2-cube for multiplicity 4,
        # a 1-cube for multiplicity 2 or 3, and 0-cube otherwise.
        size = 4 if maxcount == 4 else (2 if maxcount >= 2 else 1)
        assert lo <= 2*N//size
        histogram[lo] += 1
    assert histogram == {1: 2, 2: 134, 4: 120}
    return histogram


def mul(a, b):
    out = 0
    for _ in range(2):
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7
    return out


def times(t, a, b):
    assert len(t) > 0
    ring = {}
    for x, u in a.items():
        for y, v in b.items():
            z = tuple((i+j) % g for i, j, g in zip(x, y, t))
            ring[z] = ring.get(z, 0) ^ mul(u, v)
    return {z: a for z, a in ring.items() if a}


def lift(b):
    return {x+(i,): c for x, c in b.items() for i in (0, 1)}


def quaternary_check():
    assert mul(2, 2) == 3 and mul(2, 3) == 1
    powers = (1, 2, 3)
    D = (3, 3)
    # An explicit selector word in group basis, using field signs
    # appropriate to characteristic two.  Its four nonzero positions
    # come from two nonzero coordinates, verified by convolution below.
    b = {(r, s): mul(1 ^ powers[(-r) % 3], 1 ^ powers[(-s) % 3])
         for r, s in product(range(3), repeat=2) if r and s}
    # A parity polynomial of degree 2 with a prescribed constant on two
    # character levels. The convolution check alone establishes membership.
    parity = {(2, 0): 1, (1, 0): 1 ^ 2, (0, 0): 2 ^ 3}
    c = times(D, b, parity)
    assert c == {x: mul(3, y) for x, y in b.items()}
    assert len(b)+len(c) == 8
    bad = dict(b)
    bad[(1, 1)] ^= 1
    assert times(D, bad, parity) != {x: mul(3, y) for x, y in bad.items() if y}

    # Exact quotient transfer with characteristic dividing the kernel size.
    # The two fibers at (0,1) cancel under the coefficient push-forward.
    bigger_parity = {x+(x[0] % 2,): a for x, a in parity.items()}
    bigger_parity[(0, 1, 0)] = bigger_parity[(0, 1, 1)] = 2
    assert times(D+(2,), lift(b), bigger_parity) == lift(c)
    assert len(lift(c)) == 2*len(c) and len(lift(b)) == 2*len(b)


if __name__ == "__main__":
    h = ternary_code_census()
    print(f"PASS direct ternary module words: 256 spaces, 20480 nonzero words; "
          f"distance histogram {sorted(h.items())}")
    quaternary_check()
    print("PASS direct GF(4) convolution: signed 3-ary cube, defective-word rejection, "
          "and quotient lift through a kernel of order 2")
