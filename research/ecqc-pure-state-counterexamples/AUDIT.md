# Written-version audit and verification scope

Author: Yongxian Zhang. AI-assisted self-audit, 2026-10-08 (America/Los_Angeles).
No external professional or independent human peer review is claimed.

## Claims and proof dependencies

| Claim | Objects and proof | Computer replay | Lean status in this version |
| --- | --- | --- | --- |
| Exact pure qutrit violation, excess one bit | Actual normalized 9-dimensional vector, both partial traces, four explicit complete MUBs, every Born probability; Section 2.2 | `check_low_dimensions.py`, rational arithmetic in Q(zeta_3), symbolic logarithms | Not formalized |
| Exact pure five-dimensional violation, excess three bits | Actual normalized 25-dimensional vector, both partial traces, six MUBs and every Born probability; Section 2.3 | Same checker, arithmetic in Q(zeta_5) | Not formalized |
| Sharp ratios 3/2 and 5/2; positive qubit boundary | The above witnesses plus the established pure-state Holevo bound, applied separately in each setting; Section 2.1 | Witness sharpness checked; Holevo theorem is a cited mathematical input, not a checker hypothesis standing in for ECQC | Not formalized |
| Every prime p >= 5 has a pure counterexample | Actual embedded Bell states and canonical quadratic-phase bases; Born-law derivation, scalar minorant, Fourier moments, and rational log bound; Section 3 | Exact p=5 objects and algebraic rational identities checked by `check_exact.py`; the universal calculus and all-prime reasoning are proved in the text, not inferred from this finite replay | Not formalized |
| Unbounded overrun with one ebit | Continuous Riemann sums and explicitly evaluated integral; Section 3.2 | Not dependent on numerical quadrature | Not formalized |
| Full-Schmidt-rank qutrit witness | Actual real-integer coefficient matrix, positive marginal spectrum, common Born table, and exact integer logarithmic comparison; Section 4 | `check_low_dimensions.py` checks the matrix, spectra through annihilating polynomial and trace, all Born probabilities, and the integer sign certificate | Not formalized |
| Full Schmidt rank for every odd prime | Explicit qutrit plus displayed diagonal positive perturbations in every larger prime dimension; finite-dimensional continuity | Not an inference from finite searches | Not formalized |
| Prime-dimensional iff classification | Qubit bound plus qutrit witness plus every-prime family; all primes exhausted | Combines the indicated proofs, with no unproved bridge | Not formalized |

The ordinary spectral theorem and logarithm laws are used in the written proof and to interpret the exact certificates. The code does not replace von Neumann entropy with an assumed spectrum: it derives the marginal spectra from the actual matrices, with the polynomial/trace implications stated in the paper. Global purity follows directly from a normalized state vector and is also checked by the density-matrix identities.

## Replays actually performed

All four commands in the README completed successfully in the local Python environment. The JSON files record their exact outputs. The low-dimensional checker covers 1188 ordered basis-vector overlap tests and 222 Born probabilities across its three witnesses. The separate p=5 Bell checker covers another 900 overlaps and 150 Born probabilities. Every arithmetic operation in these checks is integer or rational; the interval checker uses rational endpoints and a proved remainder bound.

Eleven negative controls passed: malformed density normalization, an altered Born phase, a wrong Fourier moment, a product state falsely labeled as a violation, a nonpositive logarithm input, a changed qutrit amplitude, a corrupted full-rank qutrit table, a false logarithmic sign certificate, and optimized-Python rejection for each of the three main checkers. These tests detect selected errors, not all possible implementation bugs. All implementations and the audit are within the same AI-assisted research project; they are not reviews by independent mathematicians.

## Mathematical boundary checks

The ECQC score deletes a largest measured mutual information, not a smallest one. Both parties use the identical basis, not separately optimized or conjugated bases. Natural logarithms are used throughout; one bit means log(2). Full Schmidt rank refers to the reduced states, not the global density matrix, which remains rank one. Zero probabilities use the continuous 0 log(0)=0 convention. The universal upper bound assumes a pure state and is not asserted for mixed states. The large-prime lower bound is analytic and does not extrapolate numerical tests.

The exact full-rank qutrit integer difference printed on two lines in the paper was checked against the checker; the digit strings are concatenated, not added. The supplementary full-rank dimension-five example has a separate rational-interval proof and is not needed for the prime classification.

## Literature and presentation audit

The source statement was checked in Iqbal, arXiv:2509.08286v2, Conjecture 3.1, equation (6), and its closing pure-state question. The already published mixed-state counterexamples in Wang--Wang--Chen, arXiv:2608.03828v2, are explicitly credited. Neither an absolute priority claim nor a first disproof of unrestricted ECQC is made. `LITERATURE.md` records the search boundaries and excluded directions.

The LaTeX source was compiled with `latexmk -pdf -halt-on-error`. The final nine-page PDF has no overfull boxes, undefined references, or unresolved citations in the build log. All nine rendered pages were visually inspected: equations, matrices, long integer certificate, references, and page boundaries are legible without clipping or overlap. Ordinary line-wrapping of bibliography URLs does not change their targets.

## Limits

This written version does not contain a completed Lean proof of a quantum main theorem. It does not determine the optimal pure-state ratio for primes >= 7, classify all equality states, or give a full mixed-state classification. It does not contradict the original two-basis CQC theorem for pure states. Publication timestamps, commit hashes, and any later DOI identify versions and do not establish historical priority.
