"""Exact finite arithmetic checks of the local reciprocal-cutoff identity.

Represent an expression in the logs of the physical prime labels by its integer
coefficient vector. No floating point, symbolic library, or primality model is
needed. This checks the algebra, not the asymptotic sieve or Goldbach.
"""
from itertools import combinations
from math import prod


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def factors(primes):
    return {prod(p for i, p in enumerate(primes) if bits >> i & 1): bits
            for bits in range(1 << len(primes))}


def add(A, bits, weight, size):
    for j in range(size):
        A[j] += weight * ((bits >> j) & 1)


def evaluate(primes, num, den):
    n = len(primes)
    y = prod(primes)
    full = (1 << n) - 1
    subs = factors(primes)
    n0, d0 = num * num, den * den
    # Keep genuinely split orientations; no own-root or moving ties.
    if (prod(primes[:-2]) ** 2 * n0 >= y * d0 or
            prod(primes[-2:]) ** 2 * d0 <= y * n0 or
            any(b * b * n0 == y * d0 or b * b * d0 == y * n0 for b in subs)):
        return None
    actual = [0] * n
    predicted = [0] * n
    changed = 0
    small = (1 << (n - 2)) - 1
    # Direct raw and free scores, each with literal strict cutoffs.
    for a, abits in subs.items():
        root = int(a * a > y)
        low = int(a * a * n0 > y * d0)
        high = int(a * a * d0 > y * n0)
        add(actual, full ^ abits, (low - root) * (-1) ** abits.bit_count(), n)
        for c, cbits in subs.items():
            if cbits & ~small == 0 and cbits & abits == 0:
                add(actual, full ^ (abits | cbits),
                    (high - root) * (-2) ** cbits.bit_count(), n)
    # Independent complementary-short formula.
    for a, abits in subs.items():
        if a * a < y and a * a * n0 > y * d0:
            need((abits >> (n - 2)).bit_count() == 1, 'both/neither giant')
            ubits = abits & small
            sign = (-1) ** (1 + ubits.bit_count())
            for j in range(n):
                predicted[j] += sign * (1 - 2 * (ubits >> j & 1))
            changed += 1
    need(actual == predicted, (primes, num, den, actual, predicted))
    return changed


def main():
    trials = nonempty = pairs = 0
    medium = (2, 3, 5, 7, 11, 13, 17, 19)
    giants = (101, 127, 173, 257, 619, 997, 2003, 3001)
    for k in range(5):
        for core in combinations(medium, k):
            for gs in combinations(giants, 2):
                for n, d in ((21, 20), (13, 11), (5, 4), (2, 1), (4, 1)):
                    cuts = evaluate(core + gs, n, d)
                    if cuts is not None:
                        trials += 1
                        if cuts:
                            nonempty += 1
                            pairs += cuts
    need(trials >= 1000 and nonempty >= 500, (trials, nonempty))
    print(f'{trials} exact rows; {nonempty} changing rows; {pairs} split complementary pairs')


if __name__ == '__main__':
    main()
