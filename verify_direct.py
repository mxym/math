#!/usr/bin/env python3
"""Direct character sums and incidence matrices for the eight-variable witness."""

if not __debug__:
    raise RuntimeError("Run without -O")

N = 256


def omega_gf4(a):
    # Remainder of X*a modulo X^2+X+1, in polynomial-bit notation.
    z = a << 1
    return z ^ 0b111 if z & 4 else z


def permutation(y):
    u, v = y & 3, y >> 2
    rotation = omega_gf4(u) | (omega_gf4(v) << 2)
    return rotation ^ (y if (u != 0) ^ (v != 0) else 0)


def dot(x, y):
    return (x & y).bit_count() & 1


def walsh(f):
    return [
        sum(1 if f[x] == dot(a, x) else -1 for x in range(N))
        for a in range(N)
    ]


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row
                break
            row ^= pivots[j]
    return len(pivots)


def rows_of(entry):
    return [sum(entry(b, z) << z for z in range(N)) for b in range(N)]


def design_check(rows):
    assert all(r.bit_count() == 120 for r in rows)
    assert len(set(rows)) == N
    columns = [sum((row >> i & 1) << j for j, row in enumerate(rows))
               for i in range(N)]
    assert all(c.bit_count() == 120 for c in columns)
    assert all((c & columns[j]).bit_count() == 56
               for i, c in enumerate(columns) for j in range(i))
    assert all((r & rows[j]).bit_count() == 56
               for i, r in enumerate(rows) for j in range(i))


def main():
    P = [permutation(y) for y in range(16)]
    assert sorted(P) == list(range(16))
    assert all(P[P[y]] == (P[y] ^ y) for y in range(16))
    g = [dot(z & 15, z >> 4) for z in range(N)]
    h = [dot(z & 15, P[z >> 4]) for z in range(N)]
    k = [a ^ b for a, b in zip(g, h)]
    w_g, w_h, w_k = map(walsh, (g, h, k))
    assert all(w[0] == 16 and set(w) == {-16, 16} for w in (w_g, w_h, w_k))
    assert all(a * b == 16 * c for a, b, c in zip(w_g, w_h, w_k))

    T = rows_of(lambda b, z: h[z ^ b])
    A = rows_of(lambda b, z: g[b] ^ h[z ^ b] ^ k[z])
    B = rows_of(lambda b, z: h[b ^ z] ^ h[z] ^ h[b] ^ h[0])
    g_row = sum(value << z for z, value in enumerate(g))
    combination = 0
    for b in (16, 32, 48, 64, 128, 192):
        combination ^= B[b]
    assert combination == g_row

    result = tuple(map(binary_rank, (A, T, B)))
    assert result == (29, 30, 28)
    design_check(T)
    design_check(A)
    print("m=8: all 768 Walsh amplitudes and 256 dual signs PASS")
    print("m=8: both (256,120,56) designs, ranks (D,TD,core)=(29,30,28) PASS")

    # Flip one truth value: flatness and the dual-addition test must detect it.
    damaged = g.copy()
    damaged[0] ^= 1
    w_bad = walsh(damaged)
    assert any(abs(a) != 16 for a in w_bad)
    assert any(a * b != 16 * c for a, b, c in zip(w_bad, w_h, w_k))
    print("one-bit negative control PASS")


if __name__ == "__main__":
    main()
