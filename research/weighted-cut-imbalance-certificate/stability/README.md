# Near equality in weighted cut–imbalance forces a near-clique

Give the edges of a finite loopless graph nonnegative weights of total one. Let $c$ be its maximum cut, $d_i$ its weighted degrees, and $\epsilon_i$ independent fair signs. The deficit in the [weighted BEKSZ inequality](../PROOF.md) is
$$\delta=(15c-6)/4-\mathbb E\left|\sum_i d_i\epsilon_i\right|\ge0.$$

**There is a vertex set of size three or five such that changing the weighted graph into the uniform clique on that set costs at most $40{,}000{,}000\,\delta$ in total absolute edge-weight change.** This counts edges removed outside the clique and changes to each unordered pair inside it. Isolated vertices may be added. The same constant works for every graph order. It is deliberately coarse; a perturbed triangle shows the *linear dependence* itself cannot be improved to $o(\delta)$.

The two exact extremizers were [previously classified](../equality/), and the original authors already exhibited both. At a fixed graph order, a linear error bound with an order-dependent constant already follows from equality and piecewise linearity. The result here is the order-independent bound. It is not a new coding theorem or a stability result for the separate degree-square conjecture.

[Proof and constants](PROOF.md) · [Sources and earlier results](SOURCES.md) · [Internal audit](REVIEW.md)

## Reproduce the checks

Run from this folder in a checkout containing the [parent certificate](../certificate.json), using Python 3's standard library and a shell with pipefail. No optimizer or external data is needed.

~~~sh
set -eo pipefail
sha256sum -c SHA256SUMS
python -B -O verify_stability.py ../certificate.json | diff - AUTHOR-CHECKS.txt
python -B -O independent_stability.py ../certificate.json | diff - INDEPENDENT-CHECKS.txt
~~~

Both methods check all 957 polygons in the finite certificate. One uses polygon clipping; the other reconstructs vertices by intersecting rational halfspaces and directly verifies a $10^{-5}$ lower bound at each strict corner. This is AI-assisted work with independent internal AI checking, not external peer review or proof-assistant verification. Priority and the best constant are not claimed.
