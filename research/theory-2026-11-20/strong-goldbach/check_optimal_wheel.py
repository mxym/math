"""Finite checks of OptimalPrimePowerWheel.md; the asymptotic proof is analytic."""
from math import isqrt, prod


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prime(n):
    if n < 2 or (n != 2 and n % 2 == 0):
        return False
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def iroot(n, k):
    lo, hi = 1, 1 << ((n.bit_length() + k - 1) // k)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    require(lo**k <= n < (lo + 1)**k, "integer root")
    return lo


def make_wheel(n, kmax=None):
    kmax = kmax if kmax is not None else 3 * (isqrt(n.bit_length()) + 1)
    t = next(p for p in range(2*(kmax+14), 4*(kmax+14)+1) if prime(p))
    ledgers = [(2, frozenset({1})),
               (13, frozenset(set(range(1, 13)) - {a*a % 13 for a in range(1, 13)}))]
    for j, k in enumerate((k for k in range(3, kmax+1, 2) if prime(k)), 14):
        ell = j + t * (((1-j) * pow(t, -1, k)) % k)
        while not prime(ell):
            ell += k*t
        require(ell > 13 and ell % k == 1 and ell % t == j, "Linnik congruences")
        unit_powers = {pow(a, k, ell) for a in range(1, ell)}
        require(len(unit_powers) == (ell-1)//k, "size of kth-power image")
        ledgers.append((ell, frozenset(set(range(1, ell)) - unit_powers)))
    require(len({p for p, _ in ledgers}) == len(ledgers), "distinct moduli")
    require(all({-a % p for a in allowed} == allowed for p, allowed in ledgers),
            "parity of low mask")
    w = prod(p for p, _ in ledgers)

    def low(a):
        return all(a % p in allowed for p, allowed in ledgers)

    high_residues = {
        sign * pow(b, j, w) % w
        for j in range(kmax+1, n.bit_length())
        for b in range(2, iroot(n, j)+1)
        for sign in (1, -1)
    }
    deleted = {a for a in high_residues if low(a)}
    accept = lambda a: low(a) and a % w not in deleted
    require(not any(accept(a) for a in high_residues), "high-power exclusion")
    a0 = prod(sum((n-a) % p in allowed for a in allowed) for p, allowed in ledgers)
    b0 = prod(p - (1 if n % p == 0 else 2) for p, _ in ledgers)
    e = sum(low(n-a) for a in deleted)
    d = sum((n-a) % w in deleted for a in deleted)
    return w, a0 - 2*e + d, b0, accept, ledgers


def main():
    for n in range(0, 13):
        chi = 0 if n == 0 else (1 if pow(n, 6, 13) == 1 else -1)
        nonresidues = {a for a in range(1, 13) if pow(a, 6, 13) == 12}
        expected = 6 if n == 0 else (10+2*chi)//4
        require(sum((n-a) % 13 in nonresidues for a in nonresidues) == expected,
                "modulo 13 pair formula")
    n, k = 2**20, 3
    w, count, base_count, accept, _ = make_wheel(n, k)
    require(count == sum(accept(a) and accept(n-a) for a in range(w)),
            "full CRT differential check")
    for j in range(2, n.bit_length()):
        for b in range(2, iroot(n, j)+1):
            require(not accept(b**j), "integer power accepted")
    require(0 < count <= base_count, "positive pair count")
    for n in (10**16, 10**80):
        w, count, base_count, _, _ = make_wheel(n)
        require(0 < count <= base_count, "positive pair count")
        print(f"N=10^{len(str(n))-1}: {w.bit_length()} wheel bits; retained {count/base_count:.6f}")
    print("all wheel checks passed")


if __name__ == "__main__":
    main()
