# Verification and coverage

The proofs are analytic. These exact, finite, standard-library-only checks corroborate selected identities, equality cases and finite instances; they do not establish the general theorem or replace external review.

From this directory with Python 3.10 or newer:

```sh
python3 -BO check.py
python3 -BO independent.py
```

Both programs use explicit exceptions, not optimization-disabled assertions.

**First implementation.** For the following $(q,d,t)$ it enumerates every zero/projective multiplicity histogram, then compares expected rank from physical subsets with a separate grouping by surviving projective directions. At six rational erasure rates (including both endpoints), it checks optimality and the exact equality predicate for every spanning histogram.

| q,d,t | All histograms | Spanning | Erasure-rate checks |
|---|---:|---:|---:|
| 2,2,1 | 20 | 10 | 60 |
| 2,2,2 | 84 | 65 | 390 |
| 2,3,1 | 3,432 | 2,696 | 16,176 |
| 3,2,1 | 70 | 53 | 318 |

The additional enumeration of actual words and cosets checks 2,780 posterior observation fibers and 176 dual-restriction subsets in four examples. It checks 6,528 discrete Hessian entries, including every entry at the empty set, in two projective geometries.

**Second implementation.** Point/line incidence counts, without a Gaussian-elimination rank table, yield the sums of ranks of physical subsets of each possible cardinality. It exhausts 226 and 2,952 spanning multiplicity histograms for $(q,d)=(4,2)$ at $t=1,2$, and 2,696 for $(q,d,t)=(2,3,1)$. For these finite cases only, the individual rank-slice sum gaps are nonnegative and not all vanish except at the optimum. It also checks posterior fibers and dual puncturing on 64 subsets in two layouts via actual $\mathbb F_4=\mathbb F_2[z]/(z^2+z+1)$ field arithmetic, not arithmetic modulo four.

**Internal adversarial review.** A separate AI-assisted derivation counted compatible words per posterior coset, checked the sign and diagonal of the Hessian in each quotient, rederived the equality classification, distinguished randomization dimension from message dimension, and checked complement erasure rates under duality. It also supplied the [fixed-arrival proof](FIXED_DRAWS.md) and the second implementation above. This was an internal review, not a human peer review or proof-assistant formalization. Finite coefficientwise tests are not claimed to prove the general fixed-reveal-count criterion.
