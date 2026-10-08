# Source attribution and provisional originality review

This bibliography distinguishes **classical probability / information
theory tools** from the newly combined, explicitly proved quantitative
Gaussian partition inequalities. The article is not claimed to be a
world-first or externally peer-reviewed publication.

## Prior mathematics and direct predecessors

1. **OpenAI Mathematics, Gaussian propeller family 096**, 2026:
   https://github.com/openai/math .
   Context for Gaussian partitions and the squared-first-moment objective.
   Its broad global propeller results are distinct from optimizing
   exactly k prescribed equal masses at each finite k.

2. **Our all-mass Gaussian centroid envelope**:
   https://github.com/mxym/math/tree/main/research/gaussian-centroid-mass-envelope .
   Proves the sharp one-cell Gaussian halfspace bound and the
   uniform additive 2 sum p_i^2 all-mass construction, along with
   exact fixed-mass dimension stabilization.

3. **Our all-integer quadratic-dimension theorem**:
   https://github.com/mxym/math/tree/main/research/gaussian-quadratic-dimension-all-k .
   Binary linear-code Gaussian score orbit, full-rank extraction,
   exact Gaussian selector, and binary entropy <2log2.
   Previously proved D_92(k)=Theta(log^2 k). The present
   paper *quantifies the full dependence on A* and re-optimizes
   the tilted interval.

4. **Our spherical-cap converse**:
   https://github.com/mxym/math/tree/main/research/gaussian-spherical-cap-converse .
   Finite-dimensional quadratic-logarithmic defect
   k(U_k-F_d(k)) >= L^2/d-14 in its stated domain,
   yielding D_C(k)>=L^2/(C+16).
   The present paper improves the asymptotic coefficient
   by retaining the exact -log(4pi)+2 constant in both
   the Gaussian normal quantile and spherical upper bound.

## External classical ingredients

5. **I. S. Tyurin**, *A Refinement of the Remainder in the
   Lyapunov Theorem*, *Theory of Probability and Its Applications*
   **56** (2012), 693–696,
   https://doi.org/10.1137/S0040585X9798572X .
   The publisher's abstract explicitly gives upper bound
   **0.5591** for the Berry–Esseen absolute constant
   with **independent, non-identically distributed** summands.
   We use only the weaker bound 1, and separately verify
   every moment/variance hypothesis of its application.
   This is the single significant external theorem
   not reproved from first principles.

6. **Fisher–Tippett–Gnedenko / Gumbel extreme-value limit.**
   Classical Gaussian maximum asymptotics; see e.g.
   https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm .
   We do not treat distributional convergence as sufficient
   for expectation convergence: the full negative- and
   positive-tail uniform-integrability proof is included.
   The standardized Gumbel mean is the Euler constant
   \(\gamma\).

7. **Kostina and Verdú**, *Fixed-length lossy compression
   in the finite blocklength regime: Gaussian source*,
   2011 IEEE Information Theory Workshop,
   https://authors.library.caltech.edu/records/rnvhv-6k433 .
   Gaussian finite-blocklength source coding has
   significant quantitative antecedents. Our objective
   is an equal-cell-mass first-moment *partition*
   problem, not the excess-distortion probability
   in their source-coding setting; equivalence in
   historical novelty has not been assessed.

8. **Gaussian rate–distortion, normal Mills bounds,
   spherical cap union bounds, gamma log-convexity,
   binary character pairwise independence, and
   entropy chain identities** are all classical.
   Their roles are identified and proved or explicitly
   cited in paper.md; no originality claim attaches
   to any individual classical ingredient.

## Precisely established results of the current note

- A globally valid exact Gaussian extreme-value *constant*
  comparator \(k(U_k-F_\infty(k))\le2(1-\gamma)+o(1)\),
  without assuming global simplex optimality.
- A detailed spherical-cap asymptotic proving, when
  \(d/L^2\to c>0\), the lower defect
  \(\liminf k(U_k-F_d(k))\ge1/c\).
- A dimension converse at fixed additive tolerance
  \(C/k\) with asymptotic coefficient
  \(1/[C+2(1-\gamma)]\).
- A rigorously parameterized, *all-integer*
  exact-mass binary-code construction with
  \(d\le\lceil A L^2\rceil+1\) and
  explicit error function
  \(4+4\log2+2\sqrt2(5+10/\sqrt A+8/A)\).
- Seven mathematically strict integer-constant
  tradeoffs, including \((A,C)=(1,72)\),
  \((64,25)\), \((1024,22)\), \((262144,21)\).

These are assertions backed by complete written proofs
in paper.md. They establish additional quantitative
knowledge within the project, but **not** a first-in-
the-world result before an exhaustive specialist survey.

## Open boundaries

Neither the leading dimensional coefficient nor the
optimal additive constant has been identified, and
the exact finite-k Gaussian simplex extremal problem
is not settled. Gaussian quantization and source-coding
literature should be surveyed thoroughly before
a journal submission or priority assertion.
