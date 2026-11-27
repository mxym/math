# A strict tilted-CHSH Rényi tradeoff improvement

Wooltorton, Brown and Fawzi (arXiv:2605.29787v1, Corollary 5.3 and
Sections 5.2 and 6) ask which device-independent protocols can benefit
from their partially optimized Rényi entropy accumulation bound. We give
one explicit tilted-CHSH spot-checking design for which the improvement
survives **both full single-round optimizations**, with the same accepted
frequency set, over arbitrary finite-dimensional devices and quantum side
information.

In bits, for every \(0<s=\alpha-1\le 2^{-109}\), the two displayed
infrequent-sampling tradeoff objectives satisfy
\[
  h_{\mathrm{part}}(\alpha)-h_{\mathrm{down}}(\alpha)
      \ \ge\ 2^{-13}s^2>0.
\]
The accepted test threshold is strictly below the honest Bell value, so
honest acceptance tends to one. The parameters are conservative and the
explicit uniform estimate is tiny, not a practical finite-size rate claim.
At the ideal Bell-maximizing strategy the local entropy gap for
\(\alpha=2\) is about 0.0239 bits; that pointwise example is not the
tradeoff bound at \(\alpha=2\).

This is a positive, dimension-independent comparison of the two specified
bounds at the **same** Rényi order. It does not settle the paper's
Question 1 or its Section 6 question about general strategies, optimize a
final key or expansion rate, or compare against every existing EAT.

- [Proof and exact model](PROOF.md)
- [Sources and scope](SOURCES.md)
- [Deterministic checks](RESULTS.txt): run `sh replay.sh` (Python 3 and NumPy).
