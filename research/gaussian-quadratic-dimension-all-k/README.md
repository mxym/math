# Quadratic-logarithmic Gaussian dimension: all integer cell counts

**Status:** complete analytic proof with a standard, explicitly stated
Berry–Esseen theorem as external input and exact-rational proof-interface
checks. Mathematical priority or independent journal-level certification
is not asserted.

## Main result: matching dimension order for all k

Let F_d(k) be the global optimum of squared Gaussian
first-moment energy over measurable partitions of
R^d into exactly k equal Gaussian-mass cells.
Let F_infty(k) denote the dimension-saturated optimum.

**For every sufficiently large integer k**, without
any restriction that k be a power of two, we prove
the existence of an exactly equal-mass partition in

    d <= ceil((log k)^2)+1

with objective at least

    F_infty(k)-95/k.

The independent spherical-cap converse proves that
**every** partition within 95/k of this
global optimum has dimension at least

    d >= (log k)^2 / 111.

Consequently, writing D_95(k) for the smallest
dimension achieving the fixed additive error,

    D_95(k) = Theta((log k)^2)  (all large integers k).

This completes the optimal **dimension order** for
bounded additive O(1/k) approximation of the unrestricted
equal-mass Gaussian centroid problem. It does not determine
the best leading coefficient or the exact optimizer.

### Mechanism: dyadic linear codes plus binary selection

First, for dyadic k=2^r, a binary linear-code
Gaussian score orbit provides a partition in
d=ceil((log k)^2) dimensions within 100/k of
the global optimum.

For arbitrary k, decompose its binary expansion
k=q_1+...+q_s into distinct powers of two.
One independent standard Gaussian coordinate
selects block j with probability q_j/k;
within that block, a dyadic code partition in a
**shared Gaussian data block** splits into q_j
exact equal conditional masses. Every final
cell has mass exactly 1/k.

The binary-block probabilities w_j=q_j/k have
uniformly bounded entropy

    H(w) <= 4 log 2.

The global squared Gaussian hazard is 2-Lipschitz
in log tail mass, so glueing costs at most
2H(w) <=8log2 in the objective, in units of 1/k.
The mass of blocks below the dyadic threshold
is negligible for all sufficiently large k.
The local dyadic proof actually supplies a stronger
88/q bound relative to the individual halfspace
envelope (although Theorem 1 quotes the rounder
100/q corollary). Thus 88+8log2+1<95
proves the all-k 95/k theorem without requiring
source coding or numerical mass correction.

## Key mechanism

Construct a binary r-by-m generator matrix with
m=ceil((log k)^2). Associate one unit sign-vector score
to each message u in F_2^r:

    v_u(j) = (-1)^{<u,g_j>} / sqrt(m).

A full-rank generator gives a transitive group of
coordinatewise sign-flips; hence the score-maximizing
Gaussian cells have **exactly** the same measure 1/k.

The randomly sampled generator, conditional on the
Gaussian coefficient vector, produces **pairwise
independent scores for distinct nonzero messages**.
This lets a second-moment argument turn one weighted
Rademacher large-deviation estimate into a maximum
over exponentially many codewords.

The analytic heart is an exponential tilt of the
weighted Rademacher sum, with local interval mass
bounded below by the **classical independent-summand
Berry–Esseen inequality**. A conditional
Gaussian fourth-moment event controls the tilt,
and integrating exponentially improving exceedance
bounds gives a sharp expected-maximum estimate

    E max_u <v_u,G> >=
       sqrt(2 log k)
         - log(log k)/(2 sqrt(2 log k))
         - 30/sqrt(log k).

The squared first-moment objective follows from
Cauchy–Schwarz and exact codeword symmetry.
The Berry–Esseen estimate is an established
rigorous theorem, not an unverified numerical
approximation or closed-source solver output.

## Reproducibility

- [paper.md](paper.md): complete theorem, proof, constants,
  conditioning, group action and scope.
- [check_exact.py](check_exact.py): exact finite-field
  character-pair enumeration, transitivity controls,
  and rational verification of error budget constants.
- [results/check_report.txt](results/check_report.txt):
  deterministic check transcript.
- [results/check_report.json](results/check_report.json):
  machine-readable proof-interface checks.
- [AUDIT.md](AUDIT.md): mathematical proof audit.
- [LITERATURE.md](LITERATURE.md): Berry–Esseen and coding
  theory attribution; priority limitations.
- [SHA256SUMS](SHA256SUMS): source integrity manifest.

Run with Python 3 standard library:

    python3 check_exact.py
    python3 check_exact.py --json
    sha256sum -c SHA256SUMS

The exact checker verifies binary-character independence
and numeric inequalities; it **does not** attempt to
compute a giant optimal binary generator matrix or treat
a finite test as the universal proof. The latter is
fully analytical in paper.md.

## Remaining high-value work

The all-k dimension **order** is now resolved.
The next substantial problems are the sharp leading
dimension coefficient, the optimal additive constant,
and an effective algorithm for finding full-rank
binary matrices with the guaranteed Gaussian maximum.

The method also motivates finer all-mass
dimension bounds and stability classifications.
No exact fixed-k Standard Simplex optimum is claimed.

## Related work in this repository

- [Spherical-cap converse](../gaussian-spherical-cap-converse/README.md).
- [Cubic-logarithmic all-k dimension theorem](../gaussian-centroid-dimension-rate/README.md).
- [Arbitrary-mass Gaussian envelope](../gaussian-centroid-mass-envelope/README.md).
