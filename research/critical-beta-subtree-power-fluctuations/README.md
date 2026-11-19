# The fluctuation transition for power sums in critical beta-splitting trees

**Author:** Yongxian Zhang. AI-assisted mathematical research and independent AI-assisted internal review; not externally peer reviewed. The literature comparison is bounded and gives no guarantee of priority.

For each internal node of a random critical beta-splitting tree, count its descendant leaves, raise that number to a fixed real power p, and sum over the tree. Where do Gaussian fluctuations give way to non-Gaussian ones?

After centering by the exact expectation, the boundary is **p=1/2**. At the boundary the limit is still Gaussian, but its scale is √(n log³n) rather than √n. Its limiting variance on this scale is (π−4 log 2)/(12ζ(2)log²2). At every fixed 1/2<p<1 the scale becomes n^p log n and the limit is an explicit compensated block-mass martingale. At p=1 the corresponding limit is an entropy martingale and the statistic is external path length. The limits for 1/2<p≤1 have strictly positive third moments and are not Gaussian.

The p<1/2 Gaussian row (except the deterministic p=0) also follows from the earlier Brandenberger–Chin–Mossel CLT after a short verification of its moment assumptions. The p>1 centered row follows directly from the [first-order power-sum result](https://github.com/mxym/math/pull/205) and Bertoin's fragmentation area. The leading variance at p=1 was already obtained by Svihla–Lladser. The square-root threshold is not unprecedented in *other* tree models. See [source comparisons](SOURCES.md).

* [All fixed-real regimes and proofs](ALL-REAL.md)
* [Entropy limit at p=1](PROOF.md)
* [Independent internal review](REVIEW.md)
* [Exact checker](check.py) and [recorded output](CHECKS.txt). In this directory run `python3 -O check.py` and `sha256sum -c SHA256SUMS`.

The checker enumerates ordered small trees and verifies exact covariance and telescoping identities; it is not numerical evidence standing in for the asymptotic proof. There is no assertion on complex powers, moving powers at second order, or general splitting laws.
