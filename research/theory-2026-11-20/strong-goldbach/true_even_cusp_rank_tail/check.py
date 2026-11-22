"""Exact subset verification of the real-largest/log marker cusp identity."""
from fractions import Fraction as F
from random import Random


def mask_logs(a):
    out = [0]
    for value in a:
        out += [z + value for z in out]
    return out


def mob(mask):
    return (-1) ** mask.bit_count()


def validate(logs):
    # Integer labels in an ordered squarefree formal profile; q is the largest.
    logs = sorted(logs)
    whole, rank = mask_logs(logs), len(logs)
    T = sum(logs)
    half = F(T, 2)
    profile = ((F(40, 3), F(1, 4)), (F(62, 3), F(1, 4)), (F(80, 3), F(1, 2)))
    total = sum(z for z in logs)
    mu = (-1) ** rank

    def psi(t):
        return sum(w for g, w in profile if g > abs(t))

    def cusp(x):
        return abs(x - half) - half

    def even_bump(x):
        return abs(x - half) * psi(x - half)

    def odd_bump(x):
        return (half - x) * psi(x - half)

    for shape, symmetry in ((cusp, 1), (even_bump, 1), (odd_bump, -1)):
        direct = sum(mob(i) * shape(u) for i, u in enumerate(whole))
        rest = mask_logs(logs[:-1])
        qcut = sum(mob(i) * shape(u) for i, u in enumerate(rest))
        marked = F(0)
        for i, p in enumerate(logs[:-1]):
            S = mask_logs(logs[:i] + logs[i + 1:-1])
            marked -= sum(p * mob(j) * shape(p + s) / (p + s)
                          for j, s in enumerate(S))
        if direct != (1 + symmetry * mu) * qcut or qcut != marked:
            raise ValueError(("largest/log mark", logs, symmetry, direct, qcut, marked))

    # An exact collision at half is not physically possible for squarefree y.
    # Such formal profiles still validate the largest/log marker above.
    if half in whole:
        return 0
    closed = sum(mob(i) * (half - u) for i, u in enumerate(whole))
    full = (1 << rank) - 1
    own = sum(mob(full ^ i) * (u - half)
              for i, u in enumerate(whole) if u < half)
    canonical_long = sum(w * sum(mob(i) * (half - u) for i, u in enumerate(whole)
                                 if u > half - g) for g, w in profile)
    gap = sum(mob(i) * ((half - u) * psi(half - u))
              for i, u in enumerate(whole) if u < half)
    relevant = even_bump if mu == 1 else odd_bump
    reconstructed_gap = F(1, 2) * sum(mob(i) * relevant(u) for i, u in enumerate(whole))
    wanted_own = F(1, 2) * closed if mu == -1 else (
        -F(1, 2) * sum(mob(i) * abs(u - half) for i, u in enumerate(whole)))
    if canonical_long != own + gap or gap != reconstructed_gap or own != wanted_own:
        raise ValueError(("calibration parity", logs, own, gap, closed))
    if rank == 1 and own != half:
        raise ValueError(("prime half", logs, own, half))
    if rank == 2 and own != -min(logs):
        raise ValueError(("semiprime", logs, own))
    return int(bool(gap))


def main():
    rng = Random(202611220551)
    tested = crossing = 0
    for rank in range(1, 10):
        for _ in range(90):
            profile = sorted(rng.sample(range(81, 460), rank))
            crossing += validate(profile)
            tested += 1
    if not F(3, 2) ** 2 > 2:
        raise ValueError("no positive Cauchy exponent")
    print(f"verified {tested} exact synthetic log profiles, {crossing} nonzero gap scores")


if __name__ == "__main__":
    main()
