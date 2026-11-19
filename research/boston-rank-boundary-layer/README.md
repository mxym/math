# The last assignment and the additive cost of ordinary Boston

**Yongxian Zhang.** AI-assisted research note. The proof has received independent AI-assisted internal mathematical review, not external peer review. No claim of worldwide priority.

In immediate acceptance each unmatched student applies to their next school in each round. The largest rank is the round in which the final seat fills. Pritchard and Wilson asked whether its expectation grows linearly. For independent uniform rankings of n one-seat schools, the answer is yes: its expectation divided by n tends to **1 − π/sinh(π) ≈ 0.7280**. The conclusion holds under any fixed school priorities independent of the rankings.

There is also a nonconstant *joint* limit for the last rank divided by n and the realized average rank minus the harmonic number H_n. It gives an explicit convergent series for the constant C in the expected average rank H_n − C + o(1): ordinary Boston saves about **0.344 rank positions per student** compared with serial dictatorship, even though the two expected average ranks grow at the same leading rate. Ortega already proved that first-order equivalence. The additive comparison here is with serial dictatorship, not with deferred acceptance in general.

* [Complete proof and exact constant](PROOF.md)
* [Original questions and prior results](SOURCES.md)
* [Independent internal mathematical review](REVIEW.md)
* [Exact finite-case verifier](check.py) and [expected output](CHECKS.txt)

To reproduce the finite checks using only the Python standard library, run `python3 -O check.py`. The analytic proof, not the finite enumeration, establishes the limiting theorem.
