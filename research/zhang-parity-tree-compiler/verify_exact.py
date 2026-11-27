"""Small-instance exact prototype of the two compilers."""

from itertools import combinations
from random import Random


def parity(x):
    return x.bit_count() & 1


def chart_at(x, basis, y):
    for i, v in enumerate(basis):
        if (y >> i) & 1:
            x ^= v
    return x


def p_mul(a, b):
    out = 0
    while b:
        bit = b & -b
        out ^= a << (bit.bit_length() - 1)
        b ^= bit
    return out


def p_divmod(a, b):
    q = 0
    while a.bit_length() >= b.bit_length():
        j = a.bit_length() - b.bit_length()
        q ^= 1 << j
        a ^= b << j
    return q, a


def p_gcd(a, b):
    while b:
        a, b = b, p_divmod(a, b)[1]
    return a


def rat(a, b=1):
    assert b
    g = p_gcd(a, b)
    return p_divmod(a, g)[0], p_divmod(b, g)[0]


def r_mul(a, b):
    return rat(p_mul(a[0], b[0]), p_mul(a[1], b[1]))


def r_add(a, b):
    return rat(p_mul(a[0], b[1]) ^ p_mul(a[1], b[0]), p_mul(a[1], b[1]))


def r_div(a, b):
    return rat(p_mul(a[0], b[1]), p_mul(a[1], b[0]))


def r_valuation(a):
    return (a[0] & -a[0]).bit_length() - (a[1] & -a[1]).bit_length()


def rational_kernel(matrix):
    n = len(matrix)
    a = [[rat(x) for x in row] for row in matrix]
    pivots = []
    for j in range(n):
        k = next((i for i in range(len(pivots), n) if a[i][j][0]), None)
        if k is None:
            continue
        r = len(pivots)
        a[r], a[k] = a[k], a[r]
        den = a[r][j]
        a[r] = [r_div(x, den) for x in a[r]]
        for i in range(n):
            if i != r and a[i][j][0]:
                c = a[i][j]
                a[i] = [r_add(x, r_mul(c, y)) for x, y in zip(a[i], a[r])]
        pivots.append(j)
    basis = []
    for j in range(n):
        if j not in pivots:
            col = [rat(int(i == j)) for i in range(n)]
            for r, i in enumerate(pivots):
                col[i] = a[r][j]
            basis.append(col)
    return basis


def saturate_at_zero(basis, n):
    cols = [x[:] for x in basis]
    rows = []
    for i in range(len(cols)):
        options = [(r_valuation(cols[j][r]), r, j) for r in range(n) if r not in rows
                   for j in range(i, len(cols)) if cols[j][r][0]]
        _, r, j = min(options)
        cols[i], cols[j] = cols[j], cols[i]
        den = cols[i][r]
        cols[i] = [r_div(x, den) for x in cols[i]]
        for j in range(i+1, len(cols)):
            c = cols[j][r]
            cols[j] = [r_add(x, r_mul(c, y)) for x, y in zip(cols[j], cols[i])]
        rows.append(r)
    bitcols = []
    for i, col in enumerate(cols):
        assert all(not x[0] or r_valuation(x) >= 0 for x in col)
        b = sum(int(bool(x[0] and r_valuation(x) == 0)) << r for r, x in enumerate(col))
        assert (b >> rows[i]) & 1
        assert not any((b >> r) & 1 for r in rows[:i])
        bitcols.append(b)
    return bitcols


def form_anf(terms, x, basis, directions):
    j = len(directions)
    full = (1 << j) - 1
    out = 0
    for monomial in terms:
        factors = [i for i in range(monomial.bit_length()) if (monomial >> i) & 1]
        const = sum(((x >> r) & 1) << b for b, r in enumerate(factors))
        all_factors = (1 << len(factors)) - 1
        dp = {(0, 0): 1}
        for col, v in enumerate(basis):
            allowed = sum(((v >> r) & 1) << b for b, r in enumerate(factors))
            new = dp.copy()
            for (assigned, slots), c in dp.items():
                if not c:
                    continue
                avail = allowed & ~assigned
                sub = avail
                while sub:
                    for t in range(j):
                        if not ((slots >> t) & 1) and directions[t][col]:
                            key = (assigned | sub, slots | (1 << t))
                            new[key] = new.get(key, 0) ^ p_mul(c, directions[t][col])
                    sub = (sub - 1) & avail
            dp = new
        for (assigned, slots), c in dp.items():
            if slots == full and not ((all_factors ^ assigned) & ~const):
                out ^= c
    return out


def q_add(a, b, modulus):
    out = list(a) + [0] * max(0, len(b) - len(a))
    for i, c in enumerate(b):
        out[i] = (out[i] + c) % modulus
    return tuple(out)


def q_mul_binary(a, b, modulus):
    if not a or not b:
        return ()
    out = [0] * (len(a) + b.bit_length() - 1)
    for j in range(b.bit_length()):
        if (b >> j) & 1:
            for i, c in enumerate(a):
                out[i+j] = (out[i+j] + c) % modulus
    return tuple(out)


def form_walsh(walsh, n, directions):
    j = len(directions)
    den = 1 << (n + 1 - j)
    mod = den * 2
    full = (1 << j) - 1
    out = ()
    for mask, weight in walsh.items():
        if mask.bit_count() < j:
            continue
        dp = [()] * (1 << j)
        dp[0] = (1,)
        for c in range(n):
            if not (mask >> c) & 1:
                continue
            new = dp[:]
            for used, poly in enumerate(dp):
                if not poly:
                    continue
                for t in range(j):
                    if not ((used >> t) & 1) and directions[t][c]:
                        idx = used | (1 << t)
                        new[idx] = q_add(new[idx], q_mul_binary(poly, directions[t][c], mod), mod)
            dp = new
        out = q_add(out, tuple((a * weight) % mod for a in dp[full]), mod)
    assert all(c % den == 0 for c in out)
    return sum((c // den) << r for r, c in enumerate(out))


def f2_rows(rows, rhs, n):
    a = [r | (b << n) for r, b in zip(rows, rhs)]
    pivots = []
    for j in range(n):
        k = next((i for i in range(len(pivots), len(a)) if (a[i] >> j) & 1), None)
        if k is None:
            continue
        i = len(pivots)
        a[i], a[k] = a[k], a[i]
        for t in range(len(a)):
            if i != t and (a[t] >> j) & 1:
                a[t] ^= a[i]
        pivots.append(j)
    assert all(x == 0 for x in a[len(pivots):])
    v = sum(((a[i] >> n) & 1) << j for i, j in enumerate(pivots))
    ker = [(1 << f) | sum(((a[i] >> f) & 1) << j for i, j in enumerate(pivots))
           for f in range(n) if f not in pivots]
    return v, ker


def isotropic(matrix):
    r = len(matrix)
    maskrows = [sum(x << i for i, x in enumerate(row)) for row in matrix]
    def polar(u, v):
        return parity(chart_at(0, maskrows, u) & v)
    active = [1 << i for i in range(r)]
    selected = []
    while True:
        pair = next(((u, v) for u, v in combinations(active, 2) if polar(u, v)), None)
        if pair is None:
            return selected + active
        u, v = pair
        selected.append(u)
        active = [w ^ (u if polar(w, v) else 0) ^ (v if polar(w, u) else 0)
                  for w in active if w != u and w != v]


def direct_phase(terms, x):
    return sum(int(x & t == t) for t in terms) % 2


def direct_walsh(terms, n):
    vals = [(-1)**direct_phase(terms, x) for x in range(1 << n)]
    return {a: t for a in range(1 << n)
            if (t := sum(v * (-1)**parity(a & x) for x, v in enumerate(vals)))}


def restrict_walsh(w, r, a, basis):
    result = {}
    for xi, c in w.items():
        b = sum(parity(v & xi) << j for j, v in enumerate(basis))
        result[b] = result.get(b, 0) + (-1)**parity(xi & a) * c
    den = 1 << (r - len(basis))
    assert all(c % den == 0 for c in result.values())
    return {b: c // den for b, c in result.items() if c}


def compile_small(n, terms, mode, tables, given_walsh=None):
    # Exercise the contraction stages even on small instances where the
    # general degree/n cutoff could use the coordinate shortcut.
    w0 = ((given_walsh if given_walsh is not None else direct_walsh(terms, n))
          if mode == "Walsh" else None)
    j0 = len(w0).bit_length()-1 if mode == "Walsh" else max((t.bit_count() for t in terms), default=0)

    def rec(x, basis, w, j):
        r = len(basis)
        j = min(r, j)
        def linear_query(q, next_branch):
            z, _ = f2_rows(basis, [((q >> i) & 1) for i in range(r)], n)
            assert z
            flip = parity(z & x)
            return (z, next_branch(flip), next_branch(flip ^ 1))

        def phase_at(t):
            if w is None:
                return (-1)**direct_phase(terms, chart_at(x, basis, t))
            v = sum((-1)**parity(k & t) * c for k, c in w.items())
            assert abs(v) == 1 << r
            return 1 if v > 0 else -1

        if w is not None and len(w) == 1:
            q, coeff = next(iter(w.items()))
            sign = 1 if coeff > 0 else -1
            return linear_query(q, lambda b: sign * (-1)**b) if q else sign
        if j <= 1:
            if w is None:
                v = phase_at(0)
                q = sum(int(phase_at(1 << i) != v) << i for i in range(r))
                return linear_query(q, lambda b: v * (-1)**b) if q else v
            def fallback(i, word):
                if i == r:
                    return phase_at(word)
                return linear_query(1 << i, lambda b: fallback(i+1, word | (b << i)))
            return fallback(0, 0)

        anchors = [list(row[:r]) for row in tables[j]] if j > 2 else []
        unit = [[int(i == c) for c in range(r)] for i in range(r)]
        matrix = [[0] * r for _ in range(r)]
        for a, b in combinations(range(r), 2):
            ds = anchors + [unit[a], unit[b]]
            z = form_anf(terms, x, basis, ds) if w is None else form_walsh(w, r, ds)
            matrix[a][b] = matrix[b][a] = z
        u = isotropic(matrix) if j == 2 else saturate_at_zero(rational_kernel(matrix), r)
        _, query = f2_rows(u, [0] * len(u), r)
        vnew = [chart_at(0, basis, t) for t in u]
        def split(i, bits):
            if i == len(query):
                if not i:
                    return rec(x, basis, w, j-1)
                y, _ = f2_rows(query, bits, r)
                neww = restrict_walsh(w, r, y, u) if w is not None else None
                return rec(chart_at(x, basis, y), vnew, neww, j-1)
            return linear_query(query[i], lambda b: split(i+1, bits + [b]))
        return split(0, [])
    return rec(0, [1 << i for i in range(n)], w0, j0)


def tree_eval(tree, x):
    while isinstance(tree, tuple):
        q, a, b = tree
        tree = b if parity(q & x) else a
    return tree


def tree_depth(t):
    return 0 if not isinstance(t, tuple) else 1 + max(tree_depth(t[1]), tree_depth(t[2]))


def main():
    rng = Random(261103452)
    fs = [(4, [7, 9, 0]), (5, [31, 13, 21]), (5, [7, 28, 30, 2]), (5, [3, 12, 16, 0])]
    checks = 0
    for n, terms in fs:
        for r in range(2, n+1):
            for k in range(2, r+1):
                basis = [(1 << i) | (rng.randrange(1 << (n-r)) << r) for i in range(r)]
                x = rng.randrange(1 << n)
                dirs = [[rng.randrange(16) for _ in range(r)] for _ in range(k)]
                hat = restrict_walsh(direct_walsh(terms, n), n, x, basis)
                assert form_anf(terms, x, basis, dirs) == form_walsh(hat, r, dirs)
                checks += 1
    print(f"polynomial-valued ANF/Walsh contraction agreement on {checks} affine charts")
    for n, terms in fs:
        tables = {j: [[rng.randrange(1 << 19) for _ in range(n)] for _ in range(j-2)]
                  for j in range(3, n+1)}
        for mode in ("ANF", "Walsh"):
            t = compile_small(n, terms, mode, tables)
            assert tree_depth(t) <= n
            assert all(tree_eval(t, x) == (-1)**direct_phase(terms, x) for x in range(1 << n))
    print("good-seed ANF and Walsh builds: 8 complete trees verified at every point")
    def padded_cubic_walsh(n):
        return {a: (3 if not a else -(-1)**parity(a)) * (1 << (n-2)) for a in range(8)}
    n, terms = 16, [7]
    h = [[2, 4, 6] + [rng.randrange(256) for _ in range(n-3)]]
    assert 2**11 * 2**9 <= 5**9 < 2**12 * 2**9  # source bound D=12<n
    for mode in ("ANF", "Walsh"):
        t = compile_small(n, terms, mode, {3: h}, padded_cubic_walsh(n))
        assert tree_depth(t) == 3
        assert all(tree_eval(t, x) == (-1)**direct_phase(terms, x) for x in range(1 << n))
    print("padded 16-variable cubic: depth 3 in both models, below the certified cap 12")
    n = 11  # large enough that the ANF degree/n shortcut does not apply
    bad = {3: [[0] * n]}
    ta = compile_small(n, terms, "ANF", bad)
    tw = compile_small(n, terms, "Walsh", bad, padded_cubic_walsh(n))
    assert tree_eval(ta, 7) == 1
    assert tree_eval(tw, 7) == -1 and tree_depth(tw) == n
    assert all(tree_eval(tw, x) == (-1)**direct_phase(terms, x) for x in range(1 << n))
    print("zero-anchor control: ANF correctness is conditional; Walsh fallback remains exact")
    print("PASS: exact prototype")


if __name__ == "__main__":
    main()
