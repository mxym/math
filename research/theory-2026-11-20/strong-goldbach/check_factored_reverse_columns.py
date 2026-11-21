#!/usr/bin/env python3
"""Exact exponent checks for two fully specified reverse-Vaughan profiles."""
from fractions import Fraction as F
from itertools import product

THETA = F(7, 32)
WIDTH = F(1, 100_000)
EPS = F(1, 50_000)
GRID = F(1, 100_000)
BETA_LO, BETA_HI = F(".145"), F(".335")
REF_CAP = F(".466")
ASSIGNMENTS = tuple(product(range(3), repeat=4))

def profile_interval(A, p, k_of, s_left, s_right, place):
    centers = []
    for s in (s_left, s_right):
        k = k_of(s)
        v = A - s - p - k
        if not (p > v + 2 * WIDTH and v > WIDTH and k > F(".010") + WIDTH):
            raise RuntimeError("Not a genuine separated factor profile")
        if not (p + v > F(".070") + 2 * WIDTH and A - s > F(".080") + 3 * WIDTH):
            raise RuntimeError("Not on actual reverse branch")
        centers.append((s, p, v, k))
    a, b, c = [
        max(sum(vals[i] for i in range(4) if place[i] == z)
            for vals in centers) + WIDTH * place.count(z)
        for z in (0, 1, 2)
    ]
    lo = a + EPS
    hi = min(
        (1 - 8 * EPS - b - 2 * c) / 2,
        2 - THETA - 15 * EPS - a - 5 * b - 2 * c,
        (2 - 15 * EPS - a - (5 - 2 * THETA) * b - (2 + 2 * THETA) * c) / (1 + 2 * THETA),
    )
    return lo, hi

def check_profile(A, p, k_of, s_min, s_max):
    start = s_min
    n_intervals = 0
    min_join = F(1)
    while start < s_max:
        end = min(start + GRID, s_max)
        slots = [profile_interval(A, p, k_of, start, end, q) for q in ASSIGNMENTS]
        edge = BETA_LO
        while edge <= BETA_HI:
            usable = [(b, a) for a, b in slots if a < edge < b]
            if not usable:
                raise RuntimeError(("Uncovered grouped exponent", A, start, end, edge))
            nxt, low = max(usable)
            min_join = min(min_join, edge - low)
            edge = nxt
        n_intervals += 1
        start = end
    return n_intervals, min_join

def check_centering():
    # BCM exponent reserves with A at most 0.55004 and reflected a<=x^.466.
    c = F(".55004")
    g = REF_CAP + c
    if not (F(".7") * g + F(".25") * c < F(".85") - F(".001")
            and F(".875") * g + F(".125") * c < 1 - F(".001")):
        raise RuntimeError("Supercritical BC comparison failed")
    # Subcritical strips with g<1-.0001 already use true CRT.
    g = 1 - F(".0001")
    if not (F(".5") - F(".65") * g + F(".25") * c < -F(".001")
            and F(".5") - F(".625") * g + F(".125") * c < -F(".001")):
        raise RuntimeError("Subcritical BC join failed")

if __name__ == "__main__":
    profiles = (
        (F(".545"), F(".146"), lambda s: F(".210") - F(".675") * (s - F(".100")),
         F(".100"), F(".140")),
        (F(".550"), F(".145"), lambda s: F(".189"), F(".125"), F(".140")),
    )
    check_centering()
    for A, p, k_of, lo, hi in profiles:
        n_intervals, gap = check_profile(A, p, k_of, lo, hi)
        print(f"PASS A={A}, cells={n_intervals}, minimum strict cover join={gap}")
