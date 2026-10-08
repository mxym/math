# Sharp-constant Gaussian centroid dimension–accuracy tradeoffs

**Research status:** complete classical analytic proofs, exact-rational
proof-interface replay and a documented source audit. No claim of
world-first priority or machine-kernel formalization.

This note extends the [all-integer quadratic-dimension Gaussian
partition theorem](../gaussian-quadratic-dimension-all-k/README.md).
It no longer asks only whether a fixed additive error is achievable
in dimension Theta(log^2 k), but provides explicit quantitative bounds
on **how the error decreases as the coefficient of log^2 k increases**.

## Three results

Let F_d(k) be the optimal sum of squared Gaussian first moments
over **all measurable** partitions of R^d into exactly k cells
of mass 1/k, and F_infty(k)=F_(k-1)(k).
Let U_k be the sum of individually optimal one-cell Gaussian
halfspace moment scores, and gamma the Euler–Mascheroni constant.

**1. Complete constant term for the Gaussian simplex comparator.**

    0 <= limsup_{k->infty} k*(U_k-F_infty(k))
       <= 2*(1-gamma).

This does NOT assume simplex optimality. It uses the exact
regular-simplex partition and proves the required independent-normal
maximum asymptotic with uniform integrability.

**2. Improved asymptotic dimension obstruction.**

For every fixed c>0 and integer dimensions d_k with
d_k/(log k)^2->c,

    liminf k*(U_k-F_(d_k)(k)) >=1/c.

Consequently, for every fixed finite C>=0, the least dimension
D_C(k) achieving global squared-centroid objective
at least F_infty(k)-C/k satisfies

    liminf D_C(k)/(log k)^2
       >=1/[C+2*(1-gamma)].

This improves the older denominator C+16 to a fully identified
Gumbel/normal-maximum constant.

**3. Explicit all-k dimension–error Pareto family.**

For EVERY fixed A>=1, and EVERY sufficiently large integer k
(not just powers of two), there exists an exactly equal-mass
Gaussian partition in

    d <= ceil(A*(log k)^2)+1

such that

    U_k - F_d(k) <= C(A)/k,

where

    C(A)=4+4*log(2)+2*sqrt(2)*
         [5+10/sqrt(A)+8/A].

Therefore the same partition also achieves F_infty(k)-C(A)/k.

## Seven certified rational parameter choices

| Coefficient A in d<=ceil(A log^2 k)+1 | Additive error C/k |
|---:|---:|
| 1 | 72/k |
| 4 | 41/k |
| 16 | 30/k |
| 64 | 25/k |
| 256 | 23/k |
| 1024 | 22/k |
| 262144 | 21/k |

These values are verified **strictly** using only integer/rational
upper enclosures for log(2) and sqrt(2). In particular the same
A=1 dimension bound previously published with error 92/k now
works at 72/k. Allowing A=64 lowers the guaranteed error to 25/k.

The limiting bound produced by this particular construction is
4+4log(2)+10sqrt(2) (approximately 20.915); this is only a
method guarantee and is **not** established as an optimal
Gaussian quantization threshold.

## How it works

The **lower bound** uses a signed-moment comparison with a
Gaussian spherical maximum. A gamma-function cap inequality
retains the normal extreme's -loglog(k) prefactor and the
second-order curvature penalty (log k)^2/d. Normal maxima
are treated to constant order via their Gumbel limit with
an explicit uniform-integrability argument, yielding the
2(1-gamma) comparator.

The **upper construction** samples a binary full-rank linear code
at dyadic cardinalities. Conditioning on the Gaussian data
makes the nonzero character scores pairwise independent.
An exponential tilt and a published independent-summand
Berry–Esseen theorem turn this into an expected-max lower
bound. Replacing the old tilt cutoff constant 12 by 6,
and keeping m=ceil(A log^2 k) in every moment calculation,
gives the explicit new curve.

Finally a one-dimensional exact Gaussian selector glues the
binary expansion of arbitrary k. Its weights obey the **sharp
binary-selector entropy bound** H(w)<2log(2), so the gluing
uses no more than 4log(2) additional objective deficit,
in normalized units. Every cell still has mass exactly 1/k.

## Verification and scope

- [paper.md](paper.md): full analytical proofs, asymptotic
  uniform integrability, Gaussian cap expansion, and
  all parameter constants.
- [check_exact.py](check_exact.py): Python 3 standard library;
  outward-rational pi/logarithm enclosures and exact
  parameter comparisons.
- [results/check_report.txt](results/check_report.txt):
  deterministic check output.
- [results/check_report.json](results/check_report.json):
  machine-readable replay.
- [AUDIT.md](AUDIT.md): theorem dependency and correctness audit.
- [LITERATURE.md](LITERATURE.md): historical context and sources.
- [SHA256SUMS](SHA256SUMS): file integrity.

Replay:

    python3 check_exact.py
    python3 check_exact.py --json
    sha256sum -c SHA256SUMS

The checker verifies seven tradeoff pairs, fifteen highly uneven
binary selector examples, and nine large-parameter spherical-cap
thresholds using rational intervals. These finite checks are
**not proofs of universal probability theorems**. All universal
claims are established analytically in the manuscript, with a
classical Berry–Esseen theorem as an explicitly stated input.

The sharp leading coefficient of D_C(k)/(log k)^2, the exact
finite-k optimizer, stability, and fully effective code
generation remain unresolved. Specialist originality review
and external human peer review are also incomplete.
