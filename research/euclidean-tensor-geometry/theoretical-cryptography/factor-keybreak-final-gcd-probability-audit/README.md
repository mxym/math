# KeyBreak final-GCD probability audit

This note isolates one local probability-factor inconsistency in §5.4 of *Provable Integer Factorization via Multilevel Descent: Approaching Heuristic Bounds* (KeyBreak Cryptanalysis Agent, 26 November 2026).

Equation (5.4) correctly gives the conditional final-GCD success probability as
[
1-2^{1-omega(N)}.
]
The immediately following displayed lower bound (5.5) instead uses the larger factor
[
1-2^{-omega(N)}.
]
That larger factor does not follow from the preceding argument. The safe replacement is
[
(1-2^{1-omega(N)})
left[rac34(1-epsilon)-epsilon_{m pub}ight]_+.
]

This is a local correction, not a refutation of the factoring theorem. Under the paper's stated thresholds (epsilonle 1/4), (epsilon_{m pub}le 1/16), and the non-prime-power case (omega(N)ge2), the corrected expression is still at least (1/4). The later conservative epoch bound (p_0=1/128) therefore remains valid.

See `PROOF.md` for the derivation and `verify_probability.py` for an exact finite check.
