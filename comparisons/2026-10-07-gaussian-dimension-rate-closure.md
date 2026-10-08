# Gaussian centroid dimension–rate programme: sharp-order checkpoint

*7 October 2026 · public research status. Historical novelty is not yet established.*

## Main theorem: optimal dimension order for all large integers

Let
\[
F_d(k)=\sup_{\substack{(A_i)\text{ measurable partition}\\ \gamma_d(A_i)=1/k}}
\sum_{i=1}^k\left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2
\]
and write \(F_\infty(k)=F_{k-1}(k)\).
Define \(D_C(k)\) as the least dimension satisfying
\(F_d(k)\ge F_\infty(k)-C/k\).

For **every sufficiently large integer \(k\)**, without a
power-of-two restriction, the completed results establish
\[
\boxed{\displaystyle
\frac{(\log k)^2}{108}\le D_{92}(k)
\le \lceil(\log k)^2\rceil+1.}
\]
Thus \(D_{92}(k)=\Theta((\log k)^2)\).
The constants 92 and 108 are explicit proof constants, not known
optimal. No exact finite-\(k\) Standard Simplex optimum is claimed.

## Proof modules

1. [All-mass Gaussian envelope](../research/gaussian-centroid-mass-envelope/README.md):
   for exactly prescribed masses, \(0\le U(p)-M_d(p)
   \le2\sum_i p_i^2\); globally sharp 2-Lipschitz coefficient
   for the squared Gaussian upper-tail hazard in log mass.
2. [Earlier dimension-rate theorem](../research/gaussian-centroid-dimension-rate/README.md):
   balanced Gaussian threshold trees give \(O_\varepsilon(\log k)\)
   dimension for fixed relative accuracy. Cyclic Gaussian orbits
   give \(8(\log k)^3+2\) dimension for additive \(14/k\)
   accuracy. The cubic-logarithmic order is now superseded as
   the best dimension *order*; these quantitative constructions
   remain independently meaningful.
3. [Spherical-cap converse](../research/gaussian-spherical-cap-converse/README.md):
   an arbitrary equal-mass Gaussian partition with additive
   \(C/k\) accuracy must have \(d\ge(\log k)^2/(C+16)\)
   for each fixed finite \(C\), at all sufficiently large \(k\).
4. [All-integer quadratic construction](../research/gaussian-quadratic-dimension-all-k/README.md):
   binary linear-code Gaussian score orbits yield dyadic
   exact-mass partitions. A one-coordinate independent
   Gaussian selector glues the binary expansion of arbitrary
   \(k\), using the *sharp* \(H(w)<2\log2\)
   binary-block entropy inequality. The full objective
   is within \(92/k\) even of the independent one-cell
   halfspace upper envelope.

## Proof and verification status

Written analytic proofs are published for every stated theorem.
The quadratic upper bound imports only the classical
non-identically distributed Berry–Esseen bound; a primary
quantitative source is I. S. Tyurin (2012),
[DOI 10.1137/S0040585X9798572X](https://doi.org/10.1137/S0040585X9798572X),
which bounds the corresponding absolute constant by
\(0.5591<1\).

The public source includes exact-rational finite-field
character checks, binary-entropy certificates, checksum
manifests, and replayable output. **These finite checks
are not the proof of the probabilistic existence theorem**;
that theorem follows analytically using the imported
Berry–Esseen estimate and the probabilistic method.

## Remaining research frontiers

The growth order is resolved for fixed \(92/k\) accuracy, but
the sharp dimension coefficient, the smallest feasible
additive-error constant, effective polynomial-time
matrix construction, unequal-mass dimension laws,
stability, and exact finite-\(k\) optimizers remain open.
Comprehensive specialist originality review is still needed
before claiming historical priority or journal novelty.
