# AGM cycle-product containment and count correction

We prove the boxed product identity in León–Muñoz, ePrint 2025/608,
Conjecture 10.2. For every length-N nonsingular periodic solution of
v_(i+1)^2=(v_i+1/v_i)/2 (N>=2), its product w satisfies

    2^N w^2 - t w + 1 = 0,
    t an integer, t = 1 (mod 4), |t| <= 2 sqrt(2^N).

The proof works in all characteristics other than two and does not use a
characteristic-zero lift. The recurrence is normalized to ordinary AGM
isogenies. Their composition and scaling gives an endomorphism with
differential multiplier 2^N w and a fixed point of order four; the latter
determines the sign congruence.

The reverse/root-realization assertion is false for simple j-cycles: at
N=3 neither root of 8w^2-5w+1 comes from such a cycle, in any odd
characteristic or characteristic zero. Every occurrence forces a self-loop.
The literal fixed-prime count also fails, for example at p=7, which the
source allows. We prove only the boxed containment, not an equality of
root sets or a general cycle-count formula.

This is a finite-field and elliptic-curve identity, not an isogeny-path
algorithm or a result about the security of any cryptographic scheme.
Run `sh replay.sh` with Python 3, SymPy, and GNU-compatible sha256sum.
The independent finite-field checker uses only the standard library.
