# A strong Chollet inequality for every simple graph Laplacian

First public source version: 8 October 2026 UTC.

[Read the complete proof](source/proof.txt).

For every **finite simple undirected unweighted graph G**, its Laplacian L, and every vertex subset S,

    per(L[S] ∘ L[S]) ≤ per(L[S]) ∏_{v∈S} deg_G(v).

Degrees are taken in the original graph G. The empty permanent and empty product are 1. In particular,

    per(L ∘ L) ≤ per(L) ∏_v deg_G(v) ≤ per(L)².

This proves the all-graph strong and self-Chollet statements asked in Section 6 of Pant–Singh, *Structural Classes for Chollet's Permanent Conjecture*, [arXiv:2604.24192v2](https://arxiv.org/html/2604.24192v2#S6), and strengthens the strong statement to every principal submatrix. The result does not assert the conjecture for arbitrary Hermitian positive semidefinite matrices or arbitrary weighted graph Laplacians.

## Proof and review

The universal proof uses Lieb's block permanent inequality and Edmonds' matching-polytope theorem, a cycle expansion with the exact comparison 19/12 < 8/5, separate cycle and bridge cases, and closure under vertex coalescence. It includes disconnected graphs, isolated vertices, singular matrices, and the empty principal matrix. No finite computation is a proof premise.

- [Final proof](source/proof.txt), with primary references and a separate [source record](source/sources.md).
- [Independent complete audit](laplacian_chollet_independent_audit_20261008/independent_review.txt), including the precise imported hypotheses, all graph cases, source checks, and scope limits.
- [Final-copy gate](laplacian_chollet_independent_audit_20261008/FINAL_COPY_GATE.txt), binding the final text to that audit.
- [Frozen reviewed candidate](laplacian_chollet_general_20261008/proof_candidate.txt) and [exact final-copy diff](laplacian_chollet_general_20261008/final_copy_diff.txt). The final text removes the historical pending label and explicitly records diagonal normalization and positivity of the coalesced matrix. Its mathematical argument is unchanged.

This is an independent AI mathematical review and a final-copy check, not external human peer review, Lean verification, or certification of historical priority. The original bibliography and source limitations are preserved in the proof and audit. No license or personal authorship assignment is added.

## Optional exact diagnostics

The proof can be read without running these programs. For reproducible bounded diagnostics, use Python 3.10 or later with only its standard library. In a writable copy of this directory run:

```sh
python3 -B source/verify.py
python3 -B laplacian_chollet_independent_audit_20261008/check_exact.py
sha256sum --check SHA256SUMS
```

Keep the supplied directory layout. Run without `-O`, because the programs use assertions. They regenerate their adjacent JSON results. The author's program binds the final proof hash; the independent diagnostic binds the frozen candidate hash, whose final-copy diff is separately audited. Both were run in an isolated copy of this publication layout and reproduced the supplied results byte-for-byte. The independent program uses integer Ryser inclusion-exclusion and exact rational arithmetic; its 23 targeted graphs and 3,183 principal checks are auxiliary diagnostics, not extrapolation to all graphs.

The source files, their original hash lists, and all supplied results are unchanged. [MANIFEST.json](MANIFEST.json) records this version's exact identities; [SHA256SUMS](SHA256SUMS) covers the publication files. A separate GitHub Release may bind the source commit; no digital signature is asserted by these documents.
