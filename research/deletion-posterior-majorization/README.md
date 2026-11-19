# Constant observations majorize deletion-channel input posteriors

Start with a uniformly random word of length n. Reveal m letters at uniformly chosen positions, in order, but not their positions. Which observed word leaves the least uncertainty about the original word?

**Result.** For every finite alphabet and every 1≤m<n, the constant observations are exactly the minimizers of Shannon entropy. In fact, after sorting posterior probabilities from largest to smallest, the constant observation has at least as much mass in its first r entries for **every** r. This stronger order is majorization. It gives all finite positive Rényi entropy orders at once. All constant observations tie; the no-deletion and empty-observation cases are stated separately in the proof.

This resolves the **minimization** branch of the binary Atashpendar–Roscoe–Ryan conjecture on the stated uniform model. The binary min-entropy endpoint and special finite or asymptotic Shannon regimes were already known. This note does not determine the Shannon-entropy maximizers, estimate capacity, or generalize the input prior.

- [Proof](PROOF.md): express the posterior as a count of matching retention masks and align the requirements at one input position at a time. No computer verification is needed.
- [Original problem, prior results and search limits](SOURCES.md).
- [Independent internal proof review](REVIEW.md).
- [Direct retention-mask checks](CHECKS.txt) and [independent subsequence dynamic-programming checks](INDEPENDENT-CHECKS.txt).

To reproduce the finite illustrations, run `python3 -B -O verify.py` and `python3 -B -O independent.py` here. Both use only Python's standard library.

Status: AI-assisted mathematical draft, independently checked internally; no external peer review or priority certification.
