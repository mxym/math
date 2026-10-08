# Spherical-cap obstruction for Gaussian centroid partitions

**Status:** complete analytic theorem with independently replayed exact-rational
threshold tests; not a claim of historical novelty or external peer review.

This note gives a quantitative **global dimension lower bound** for
equal-mass Gaussian centroid partition optimization. It strengthens
the earlier entropy/rate–distortion converse and closes the loglog
factor in its necessary dimension order.

## The main theorem

Let F_d(k) be the supremum of the sum of squared Gaussian cell
first moments over all measurable partitions of R^d into exactly k
cells, each having Gaussian mass 1/k. Let U_k be k times the
square of the one-dimensional Gaussian density at the upper
1/k quantile (the sum of individually best halfspace cell
centroid scores). Set L=log k.

For every k with L>=100, and every integer
d>=L^2/log L, we prove the explicit inequality

    U_k - F_d(k) >= [L^2/d - 14]/k.

This holds over **all measurable partitions**: no assumptions on
region shape, conical structure, orthogonality, symmetry or
existence of an attaining maximizer.

Combining this with the previously certified high-dimensional
construction U_k-F_infty(k)<=2/k yields:

    If F_d(k) >= F_infty(k)-C/k
    for every sufficiently large k, then
    d >= [log(k)]^2/(C+16).

Consequently additive O(1/k) approximation of the
unrestricted k-cell optimum **requires dimension Omega(log^2 k)**.

The independently published cyclic-orbit construction supplies
dimension at most 8(log k)^3+2 for additive 14/k error.
Thus, at fixed bounded additive tolerance, the present
necessary and sufficient scales lie between
log^2 k and log^3 k.

## Proof architecture

1. Each equal-mass Gaussian cell has first moment bounded
   by the sharp individual halfspace rearrangement.
   Normalizing all cell first moments converts their score
   into an expected maximum of k Gaussian linear forms.
2. Polar decomposition writes the latter maximum as
   Gaussian radius times a maximum of k spherical projections.
3. The exact first-coordinate spherical density and gamma
   log-convexity yield a spherical-cap union bound including
   its critical **1/s** prefactor.
4. Choosing a radius threshold with squared value
   2L-log L-2L^2/d+16 and integrating the tail preserves
   **both** the -log L correction and the dimensional
   2L^2/d loss.
5. A simple squared-difference identity converts the
   Gaussian maximum ceiling into an additive centroid
   deficit. The dimension theorem follows by comparison
   to the known 2/k global halfspace envelope.

This improves the older information-theoretic obstruction
(2-o(1))log^2(k)/loglog(k) to order log^2(k).
It does **not** prove an O(log^2 k) matching
constructive upper bound.

## Reproducibility

- [paper.md](paper.md): complete self-contained proof.
- [check_exact.py](check_exact.py): rational log/pi and
  spherical-cap threshold checker (Python 3 standard library).
- [results/check_report.txt](results/check_report.txt):
  fixed public replay output.
- [results/check_report.json](results/check_report.json):
  machine-readable replay.
- [AUDIT.md](AUDIT.md): detailed proof audit and trust limits.
- [LITERATURE.md](LITERATURE.md): provenance and novelty caution.
- [SHA256SUMS](SHA256SUMS): immutable content verification manifest.

To replay:

    python3 check_exact.py
    python3 check_exact.py --json
    sha256sum -c SHA256SUMS

The 12 rational examples include k=10^44, 10^75,
10^200 and 10^1000, with three dimension choices
per k, including the narrow lower regime
d=ceil(L^2/log L). All numerical claims in
these tests have rational interval certificates.
The *universal* results are proved analytically,
not by enumeration.

## Upstream and continuity

- OpenAI Mathematics result 096:
  https://github.com/openai/math
- Companion arbitrary-mass envelope:
  https://github.com/mxym/math/tree/main/research/gaussian-centroid-mass-envelope
- Previous constructive dimension-rate result:
  https://github.com/mxym/math/tree/main/research/gaussian-centroid-dimension-rate

The strong Gaussian one-cell bound and all-mass
high-dimensional construction are inherited,
clearly attributed, and used with exact hypotheses.
