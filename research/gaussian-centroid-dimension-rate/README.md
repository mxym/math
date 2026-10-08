# Gaussian centroid dimension–rate theorem

**Status:** complete analytic derivations with reproducible exact-rational
checks, prepared as an independently attributed research note.
No mathematical world-first or journal-priority claims are made.

This note studies the exact number of Gaussian coordinates needed
to approximate the **global** squared first-moment optimum over
measurable partitions into \(k\) cells, each of Gaussian mass \(1/k\).
It complements OpenAI Mathematics 096 (Gaussian propeller) and
the published all-mass envelope in this research repository.

## Main two-scale result

For every fixed \(0<\varepsilon<1\) and all sufficiently large
integers \(k\), there exists an **explicit** exactly
equiprobable \(k\)-cell Gaussian partition in
\(d\le C_\varepsilon\log k\) dimensions whose squared-centroid
objective is at least \(1-\varepsilon\) times the unrestricted
optimum in all Gaussian dimensions. The construction works
for every large integer \(k\), not only perfect powers.

The converse proves that this is the correct dimensional order:
every \((1-\varepsilon)\)-optimal equal-mass Gaussian partition
requires \(d\ge(c_\varepsilon-o(1))\log k\), where
\(c_\varepsilon>0\) is the unique solution of

    (c/2) * (1 - exp(-2/c)) = 1 - epsilon.

This is obtained from the sharp Gaussian
**mutual-information / rate–distortion converse**

    F_d(k) <= (d/k) * (1 - k**(-2/d)),

valid for **all** measurable equal-mass partitions in \(\mathbb R^d\).

A substantially stronger necessary dimensional scale arises if
the target is **additive \(O(1/k)\) accuracy**, rather than
constant-relative accuracy:

    d >= (2-o(1)) * (log k)**2 / log(log k).

No matching constructive upper dimensional bound at this second
scale is claimed; identifying it is the primary next problem.

## Proof mechanism

A balanced b-ary tree of integer leaf counts gives exactly
\(k\) equally likely target labels. Every level uses a fresh
Gaussian block of dimension \(b-1\), **shared across all nodes
at that level**. At each node a sequential Gaussian quantile
partition realizes its integer child proportions exactly.

An analytic lower bound on the conditional Gaussian
centroid energy of each b-way node, and the additivity of
independent-coordinate mean energies, give

    P_tree(k,b) >= (ceil(log_b k)-1) * L_b/k,

with

    L_b = 2 log(b/2) - log(log(2*b)) - 6.

Since \(L_b/(2\log b)\to1\), choosing a sufficiently large
constant b gives any fixed relative accuracy in
\(O_\varepsilon(\log k)\) dimensions.

For perfect powers \(k=b^t\), a second exact family built
from products of regular-simplex Gaussian partitions gives

    P_simplex-product =
        t * b/(b-1) * (E max_{1<=j<=b} Z_j)**2 / k,

in exactly \(t(b-1)\) dimensions.

The note also proves an **exact method barrier**:
for the previously published one-pass staircase at equal
masses,

    lim_{k->infty} k*(U_k - P_staircase(k)) = 2,

where U_k is the sum of individual Gaussian halfspace
centroid ceilings. This identifies why simply improving
the estimates for that fixed construction cannot
improve its universal additive 2/k asymptotic gap.
It is **not** a lower bound on the true global optimum.

## Verification and reproducibility

- [paper.md](paper.md): full theorem statements, analytic
  arguments, special cases and boundary conditions.
- [check_exact.py](check_exact.py): pure Python 3 standard library;
  outward-rounded rational logs and exponentials, exact integer
  tree-count verification, and a set of certified parameter cases.
- [results/check_report.txt](results/check_report.txt): exact
  output of the default verifier.
- [AUDIT.md](AUDIT.md): proof-scope and dependency audit.
- [LITERATURE.md](LITERATURE.md): prior-work context and
  unverified historical originality claims.
- [SHA256SUMS](SHA256SUMS): integrity manifest.

Run:

    python3 check_exact.py
    python3 check_exact.py --quick
    sha256sum -c SHA256SUMS

All Gaussian analysis is proved **symbolically** in paper.md.
The finite tests are separate replayable cross-checks,
not substitutes for proofs of universal statements.

## Important scope

The result concerns **the first Hermite level**
(squared Gaussian centroids), not full noise stability
at arbitrary fixed nonzero correlation. Standard Gaussian
rate–distortion and vector-quantization results have
historical priority for key information-theoretic
ingredients. We do not claim to settle the Standard
Simplex Conjecture or any exact finite-k optimizer.

The exact nonasymptotic mass-envelope companion is
[Gaussian centroid mass envelope](../gaussian-centroid-mass-envelope/README.md).
The planar fan and dimension-saturation companion is
[Gaussian propeller balanced fans](../gaussian-propeller-balanced-fans/README.md).
