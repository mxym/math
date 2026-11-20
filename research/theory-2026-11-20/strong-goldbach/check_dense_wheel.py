"""Finite differential check of the block mask; not an analytic estimate."""

from math import gcd, isqrt, prod


def require(condition, label):
    if not condition:
        raise ValueError(label)


def check(n):
    blocks = ((2, (5, 13)), (3, (7, 19)))
    moduli = [2] + [p for _, primes in blocks for p in primes]
    w = prod(moduli)
    data = []
    for k, primes in blocks:
        powers = {p: {pow(x, k, p) for x in range(1, p)} for p in primes}
        data.append((primes, powers))
        require(all(len(powers[p]) == (p - 1) // k for p in primes), "group order")

    def h(a, block):
        primes, powers = block
        return all(a % p in powers[p] for p in primes)

    def initial(a):
        return gcd(a, w) == 1 and not any(h(a, block) for block in data)

    base = set(range(w))
    pair_units = {a for a in base if gcd(a * (n-a), w) == 1}
    a0 = 1
    for block in data:
        primes, powers = block
        q = prod(primes)
        ordinary = prod(p - (1 if n % p == 0 else 2) for p in primes)
        subgroup = prod(len(powers[p]) for p in primes)
        onto_units = sum(h(a, block) and gcd(n-a, q) == 1 for a in range(q))
        both = sum(h(a, block) and h(n-a, block) for a in range(q))
        a0 *= ordinary - 2*onto_units + both
        require(ordinary - 2*onto_units + both >= ordinary - 2*subgroup, "union estimate")
    require(a0 == sum(initial(a) and initial(n-a) for a in pair_units), "CRT")
    powers_through_n = set()
    high = set()
    for b in range(2, isqrt(n)+1):
        exponent, value = 2, b*b
        while value <= n:
            powers_through_n.add(value)
            if exponent > 3:
                high.add(value)
            exponent, value = exponent+1, value*b
    e = {sign * value % w for value in high for sign in (1, -1) if initial(sign*value)}
    accept = lambda a: initial(a) and a % w not in e
    require(all(accept(a) == accept(-a) for a in base), "evenness")
    require(not any(accept(value) for value in powers_through_n), "remove powers")
    expected = a0 - 2*sum(initial(n-a) for a in e) + sum((n-a) % w in e for a in e)
    require(expected == sum(accept(a) and accept(n-a) for a in pair_units) > 0, "deleted pair count")
    return len(e)


def main():
    require(max(check(n) for n in (2048, 3072, 3990, 4096)) > 0, "nontrivial deletion control")
    print("Dense wheel: exact CRT, parity and power controls passed.")


if __name__ == "__main__":
    main()
