"""Check the reduced trace equations and an explicit n=3 extension (stdlib only)."""
from itertools import combinations

# f(t) monic irreducible, binary coefficient encoding (lsb = constant).
POLY = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011,
        5: 0b100101, 6: 0b1000011}


def require(test, message):
    if not test:
        raise ValueError(message)


def arithmetic(n):
    mod = POLY[n]
    q = 1 << n

    def mul(x, y):
        z = 0
        while y:
            if y & 1:
                z ^= x
            x <<= 1
            if x & q:
                x ^= mod
            y >>= 1
        return z

    def trace(x):
        y = 0
        for _ in range(n):
            y ^= x
            x = mul(x, x)
        require(y in (0, 1), "absolute trace not binary")
        return y

    for a in range(1, q):
        require(len({mul(a, b) for b in range(q)}) == q, "not a field")
    return mul, trace


def rank(rows):
    pivots = {}
    for x in rows:
        while x:
            k = x.bit_length() - 1
            if k not in pivots:
                pivots[k] = x
                break
            x ^= pivots[k]
    return len(pivots)


def check(n):
    q = 1 << n
    mul, tr = arithmetic(n)
    m = n * (q - 1)  # a[0] fixed to zero
    rows = []
    for b, c in combinations(range(q), 2):
        s = sum(tr(mul(b ^ c, 1 << j)) << j for j in range(n))
        row = (s << ((c - 1) * n)) ^ ((s << ((b - 1) * n)) if b else 0)
        rows.append(row)
    r = rank(rows)
    ra = rank((x << 1) | 1 for x in rows)
    count = 0 if r != ra else 1 << (m - r)
    require((count > 0) == (n <= 3), "unexpected decision")
    gram = [
        ((1 << (q - 1)) - 1) ^ (1 << i) for i in range(q - 1)]
    require(rank(gram) == q - 2, "Gram rank")
    print(f"n={n}, equations={len(rows)}, ranks={r}/{ra}, normalized assignments={count}")
    if n == 3:
        inv = [0] + [next(y for y in range(1, q) if mul(x, y) == 1)
                     for x in range(1, q)]
        require(all(tr(mul(b ^ c, inv[b] ^ inv[c]))
                    for b, c in combinations(range(q), 2)), "inverse example")
        print(f"n=3 inverse witness a={inv}")


if __name__ == "__main__":
    for n in POLY:
        check(n)
