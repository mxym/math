"""Finite checks of the marker construction; the asymptotic proof is in README.md."""
import itertools


def parameters(q, n):
    if q < 2:
        raise ValueError("q must be at least two")
    power, b = 1, 0
    while power * q <= n:
        power *= q
        b += 1
    if b < 2 or n <= 4 * b:
        raise ValueError("use q >= 2, b >= 2, and n > 4b")
    return b, power * power // n


def integer(word, q):
    value = 0
    for digit in word:
        value = value * q + digit
    return value


def words(q, n):
    b, cutoff = parameters(q, n)
    m = 2 * b
    base = (0,) * (b - 1) + (1,)
    alphabet = range(q)
    for prefix_code in range(cutoff):
        code = prefix_code
        continuation = [0] * b
        for i in range(b - 1, -1, -1):
            code, continuation[i] = divmod(code, q)
        for middle in itertools.product(alphabet, repeat=n - m - 1):
            for last in range(1, q):
                word = base + tuple(continuation) + middle + (last,)
                if any(word[j : j + b] == base and
                       integer(word[j + b : j + m], q) < cutoff
                       for j in range(1, n - m + 1)):
                    continue
                if any(word[n - k : n - k + b] == base
                       for k in range(b, m)):
                    continue
                yield word


def verify(q, n):
    prefixes = [set() for _ in range(n)]
    suffixes = [set() for _ in range(n)]
    count = 0
    for word in words(q, n):
        for length in range(1, n):
            prefixes[length].add(word[:length])
            suffixes[length].add(word[-length:])
        count += 1
    assert all(p.isdisjoint(s) for p, s in zip(prefixes, suffixes))
    print(f"q={q} n={n} codewords={count}")


if __name__ == "__main__":
    for n in (13, 14, 15, 17, 18, 19, 20):
        verify(2, n)
    for n in (9, 10, 11, 12):
        verify(3, n)
