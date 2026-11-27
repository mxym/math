# Reusing a universal hash seed: a sharp linear-in-block-count tail

Let a public seed be sampled independently of a finite
classical–quantum source, then reused to hash \(k\) raw blocks.
Condition the entropy of every raw block on **all earlier raw
blocks and the quantum side register**. If these conditional
min-entropies are all at least \(h\) bits, and the output alphabet
has size \(m\), two-universal hashing gives
\[
 \Pr_f\left[\tfrac12\|\rho_{Z^kE}^{\,f}
                         -U_m^{\otimes k}\otimes\rho_E\|_1
                    \ge \delta\right]
 \le \min\!\left\{1,\frac{k\,\ln(1+(m-1)2^{-h})}{2\delta^2}\right\}.
\]
There is no conditional independence or stationarity requirement.
The theorem uses the real side-information marginal, not a
minimization over an arbitrary ideal-side state. The expected
squared fixed-seed distance obeys the same law without
\(1/\delta^2\), giving an average trace-distance bound of order
\(\sqrt{k}\) at fixed one-block entropy. These statements concern
a fixed, seed-independent joint input state, not an adaptive
source which learns the seed and then changes its inputs.

Chung and Vadhan's classical shared-seed theorem already
gives square-root block-count scaling (arXiv:0806.1948, Theorem
3.8). The present result extends that scale to quantum side
information, using the true side marginal and a fixed-seed tail,
also for almost two-universal hashing. A simple classical binary
family illustrates that a linear tail coefficient cannot in general
be improved in order; this classical obstruction is not claimed new. For exact conditional independence
and marginal stationarity, an additional structural result gives
a classical conditional-i.i.d. representation and a pointwise
coupling bound. We do not claim to characterize all models that
permit seed reuse, or certify any implementation.

[PROOF.md](PROOF.md) states the general collision-based and almost
two-universal bounds and proves them, the lower bound, and the
structural corollary. [SOURCES.md](SOURCES.md) distinguishes the
contributions from the one-block and previous blockwise results.
Two toy verifiers use exact rational arithmetic and bounded
square-root intervals; they illustrate the formulas, not replace
the proofs.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
