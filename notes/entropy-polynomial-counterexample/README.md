# A counterexample to Wakhare's entropy polynomial root conjecture

First public source version: 8 October 2026 UTC.

[Read the complete proof](COUNTEREXAMPLE_PROOF.md). For the admissible coprime pair **(k,r)=(11,10)**, the polynomial in Conjecture 2 of Tanay Wakhare's *Iterated Entropy Derivatives and Binary Entropy Inequalities* has **at least four distinct roots in (0,1)**. Exact integer/rational comparisons establish signs +, −, +, −, + at 1/5, 2/5, 3/5, 2/3, 4/5; continuity supplies four disjoint root intervals. This contradicts the asserted total of exactly two roots, even counting multiplicity.

## Proof and independent check

- [Complete Markdown proof](COUNTEREXAMPLE_PROOF.md), including the defining binomial sums, exact coefficient lists, rational alpha enclosure and full positive integer residuals.
- [Primary exact checker](verify_small_counterexample.py) and [certificate](small_exact_certificate.json).
- [Independent audit](independent/AUDIT.md), [independent integer-only checker](independent/verify_small_integer.py), and [independent certificate](independent/small_integer_certificate.json). The auditor reconstructed the formulas independently; the proposed parameters and test points had been supplied.
- The audit's larger (20,19) cross-check is retained as [standalone code](independent/verify_integer.py), [full integer certificate](independent/integer_certificate.json), and [compact rational certificate](independent/compact_certificate.json).

## Reproduce

Use Python 3.11 or later, with only the standard library. In a writable copy of this directory run:

```sh
python3 -B verify_small_counterexample.py
python3 -B independent/verify_small_integer.py
python3 -B independent/verify_integer.py
sha256sum --check SHA256SUMS
```

Run normally, without `-O`: the checks use Python assertions. They regenerate the adjacent certificate files. For this release all three programs completed and reproduced all four supplied certificate files byte-for-byte in an isolated copy. No floating-point root solver or numerical optimization enters the proof. The original audit's ancillary stdout logs are not included; these unchanged scripts regenerate their run summaries.

## Exact claim and publication record

The conclusion is at least four distinct interior roots. It is not a claim of exactly four, smallest parameters, root multiplicities, an infinite family, or certified priority. It refutes Conjecture 2 only; it does not refute Conjecture 1, Ho's separate entropy-inequality result, or settle Frankl's union-closed sets conjecture. This commit contains a written proof and exact arithmetic evidence, **not a completed Lean verification**. A typeset PDF and any later formal development are separate work.

The target is Wakhare's Conjecture 2, equations (1.3)–(1.4), [arXiv:2312.14743v2](https://arxiv.org/abs/2312.14743v2), published in Journal of Approximation Theory 307 (2025), 106143, [DOI 10.1016/j.jat.2025.106143](https://doi.org/10.1016/j.jat.2025.106143). The proof and audit retain their exact source-comparison and literature-search limits. No professional human peer review or novelty certification is asserted.

[MANIFEST.json](MANIFEST.json) binds this version's files and verification roles. [SHA256SUMS](SHA256SUMS) records byte-integrity hashes. Hashes identify content; no digital signature is asserted by this source package. No license or personal authorship assignment is added.
