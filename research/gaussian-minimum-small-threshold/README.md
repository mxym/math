# Gaussian minima: the small-threshold part of Kunisky's cosine covariance conjecture

How should the correlations of n standard normal coordinates be arranged to maximize the chance that **at least one coordinate lies within t of zero**? For each fixed n, this note proves that all sufficiently small positive t have the same optimizer: the coordinates are projections of a two-dimensional Gaussian onto n evenly spaced lines. Equality allows only reordering the coordinates and reversing their signs.

The cutoff is common to **all** competing correlation matrices at a fixed n, including singular matrices and competitors that change with t. We do not give a numerical cutoff or prove the [conjecture](https://arxiv.org/html/2605.02023v1#S3) for every t. The all-threshold planar comparison is [already known](https://doi.org/10.5281/zenodo.23453252).

- [Proof](PROOF.md): a limiting count of rank-two strip overlaps gives the sharp second-order union loss and confines near-optimizers to a regular planar configuration. A strict estimate for off-plane offsets then proves the exact inequality on a whole interval.
- [Sources and limits of the prior-art search](SOURCES.md), including the earlier planar result and the same signed-cycle operator for a moment functional.
- [Independent internal mathematical review](REVIEW.md). The reviewed source was subsequently edited to add attribution and change Markdown delimiters; the proof equations and arguments are unchanged.
- [Optional finite diagnostics](verify.py) and [expected output](CHECKS.txt): run `python3 -B -O verify.py`. These are exact sanity checks, not a numerical or formal proof of the continuous theorem. File digests are in `SHA256SUMS`.

AI-assisted work, internally reviewed by a separate AI reader. Not externally peer reviewed, not formally verified, and with no first-priority claim.
