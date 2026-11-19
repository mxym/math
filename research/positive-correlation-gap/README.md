# The sharp correlation gap under nonnegative pairwise covariance

**Yongxian Zhang.** AI-assisted research note; independently reviewed internally with AI assistance, not externally peer reviewed. No claim of worldwide priority.

Suppose one chooses a random subset with specified probabilities of including each element, and the payoff never decreases when an element is added. How much is lost if each pair of elements must occur together at least as often as it would under independence?

**At most one quarter of the optimal expected payoff is lost, and the bound is sharp.** The same random transformation works simultaneously for every nonnegative increasing payoff, not just submodular ones. It preserves each inclusion probability, retains every original element together with probability at least 3/4, and ensures that every upper intersection has probability at least the product of its marginals.

For sharpness take two elements, each present with probability 1/2, with payoff 1 for a nonempty subset. Without the pair constraint one can always choose exactly one; with it, the best probability of a nonempty subset is 3/4. The corresponding worst-case ratio, unrestricted over restricted, is **4/3**.

* [Finite-set theorem and proof](PROOF.md), including why requiring positive association instead is different.
* [Exact interpolation](GENERAL.md) for general lower bounds on pair intersections, up to comonotonicity.
* [Arbitrary real marginals](REAL.md): a sharp comparison for increasing objectives under **positive upper orthant dependence**, not simultaneous upper and lower orthant dependence.
* [Original suggestion and related results](SOURCES.md), [internal mathematical review](REVIEW.md), [exact finite checks](check.py) and [expected output](CHECKS.txt).

The original September 2026 paper suggested allowing positive correlations as a relaxation of pairwise independence; it did not state a formal conjecture with a particular multivariate dependence definition. **Pairwise independence itself is a different restriction:** the asymptotic worst-case gap for submodular functions in that model is already known to be e/(e−1).

To replay the finite checks, run `python3 -O check.py` (standard library). The general theorem follows from the analytic coupling, not from numerical optimization.
