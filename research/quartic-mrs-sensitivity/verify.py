#!/usr/bin/env python3
"""Integer max-plus recurrence and separate truth-table check."""

from math import gcd

L = 4
SIZE = 1 << (2 * L)
NEG = -10**9
A = (0, 1, 2, 4)
B = (0, 1, 3, 4)
DEFICITS_A = (0, 2, 1, 1, 2, 1)
CORRECTIONS_B = (0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8)


def check(test, msg):
    if not test:
        raise ValueError(msg)


def direct_sensitivity(S, n):
    """Distinct orbit convention. Evaluate ANF and all single-bit flips."""
    orbit = {sum(1 << ((i + j) % n) for j in S) for i in range(n)}
    values = [sum((v & m) == m for m in orbit) & 1 for v in range(1 << n)]
    return max(sum(values[v] != values[v ^ (1 << j)] for j in range(n))
               for v in range(1 << n)), len(orbit)


def transitions(S, p, q):
    """Edges of the normalized recurrence; high-order bits are earlier."""
    targets = [[] for _ in range(SIZE)]
    for u in range(SIZE):
        for e in (0, 1):
            full = 2*u + e
            support_value = 0
            for a in S:
                hit = 1
                for b in S:
                    if b != a:
                        hit &= (full >> (L - (b - a))) & 1
                support_value ^= hit
            v = full % SIZE
            targets[v].append((u, q*support_value - p))
    check(all(len(x) == 2 for x in targets), "not a de Bruijn graph")
    return targets


def maxplus_powers(weights, N):
    """One update per final vertex using its two possible predecessors."""
    A = [[0 if i == j else NEG for j in range(SIZE)] for i in range(SIZE)]
    for k in range(1, N + 1):
        B = []
        for row in A:
            out = []
            for (x,w), (y,v) in weights:
                lhs = row[x] + w if row[x] != NEG else NEG
                rhs = row[y] + v if row[y] != NEG else NEG
                out.append(max(lhs, rhs))
            B.append(out)
        A = B
        yield k, A


def candidate_a(n):
    return n - DEFICITS_A[n % 6]


def candidate_b(n):
    k,r = divmod(n,11)
    return 10*k + CORRECTIONS_B[r]


def prove_case(S, p, q, start, period, predicted):
    values = {}
    record = None
    for n, matrix in maxplus_powers(transitions(S,p,q),start+period):
        diag = max(row[i] for i,row in enumerate(matrix))
        check((diag+p*n)%q==0, "arithmetic mismatch")
        if n >= 9:
            value = (diag+p*n)//q
            check(value == predicted(n), f"bad formula at n={n}")
            values[n] = value
        if n == start:
            record = matrix
        if n == start+period:
            check(record is not None and record == matrix, "whole matrices differ")
    print(f"PASS {S}: C^{start}=C^{start+period} at all {SIZE**2} entries;"
          f" finite diagonal values n=9..{start+period}: {list(values.values())}")


def anfs_with_at_most(S, n, cap):
    """Independent prefix search over actual distinct ANF. No matrix or memoization."""
    orbit = {sum(1 << ((i + j) % n) for j in S) for i in range(n)}
    groups = [[] for _ in range(n)]
    for j in range(n):
        bit = 1 << j
        terms = tuple(m ^ bit for m in orbit if m & bit)
        # The final variable on which any term of this derivative depends.
        last = max(terms).bit_length()-1
        groups[last].append(terms)

    def search(word, assigned, misses):
        if assigned:
            for terms in groups[assigned-1]:
                misses += (sum((word & a) == a for a in terms) & 1) == 0
        if misses > cap:
            return -1
        if assigned == n:
            return word
        zero = search(word,assigned+1,misses)
        if zero >= 0:
            return zero
        return search(word | (1 << assigned),assigned+1,misses)

    return search(0,0,0)


def confirm_independently(S, stop, predicted):
    # Every cutoff branch is impossible by the immutable sum of already
    # completed derivative failures. Check existence and rule out improvement.
    for n in range(9,stop+1):
        misses = n-predicted(n)
        check(anfs_with_at_most(S,n,misses)>=0,("missing witness",S,n))
        check(anfs_with_at_most(S,n,misses-1)<0,("better truth assignment",S,n))
    print(f"PASS independent ANF branch search on all n=9..{stop} for {S}.")


def main():
    print(f"A: s(n)=n-d[n mod 6] for n>=9; d={DEFICITS_A}")
    print(f"B: s(n)=10 floor(n/11)+e[n mod 11] for n>=7; e={CORRECTIONS_B}")
    prove_case(A,1,1,27,6,candidate_a)
    prove_case(B,10,11,31,11,candidate_b)
    for S, expected, orbits in ((A,(4,6,4,7),(5,6,7,8)),
                               (B,(4,4,6,7),(5,3,7,8))):
        out = [direct_sensitivity(S,n) for n in range(5,9)]
        check(tuple(v for v,n in out)==expected and tuple(n for v,n in out)==orbits,
              "failed direct truth-table edge case")
        print(f"PASS {S}: n=5..8 exact (sensitivity, #orbit terms) = {out}")
    for S in (A,B):
        for n,t in ((12,2),(15,3),(16,2)):
            d = gcd(n,t)
            m = n//d
            if m<=4:
                continue
            got,_ = direct_sensitivity(tuple(t*x for x in S),n)
            s,_ = direct_sensitivity(S,m)
            check(got==d*s, "coprime decomposition check")
    print("PASS three direct dilation checks per support where offsets remain distinct.")
    confirm_independently(A,33,candidate_a)
    confirm_independently(B,42,candidate_b)
    alleged_nine = anfs_with_at_most(B,9,0)
    check(alleged_nine<0, "negative control accepted a fabricated full-sensitivity claim")
    corrupt = transitions(B,10,11)
    (u,w),(v,z) = corrupt[0]
    corrupt[0] = [(u,w+25),(v,z)]
    mutated = {n: M for n,M in maxplus_powers(corrupt,42) if n in (31,42)}
    check(mutated[31] != mutated[42], "negative control accepted altered matrix weights")
    print("PASS two negative controls: false ANF optimum and corrupted matrix weight both rejected.")


if __name__ == "__main__":
    main()
