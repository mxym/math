# Bounded cluster avoidance for uncountable selector families

[Complete proof](paper.md) · [PDF](paper.pdf) · [Editable LaTeX](paper.tex) · [Independent proof audit](PROOF_AUDIT.md) · [Source provenance](../avoidance-covering-provenance/README.md)

For bounded finite clusters occupying a positive-upper-Banach-density set of logarithmic scales, one large closed periodic set excludes every pointwise selector simultaneously, with the prescribed countable null-modulus perturbations. Successful clusters lie wholly in the small open complement. The finite-alphabet/profile corollary includes uncountably many arbitrary switching functions.

The proof assumes a fixed finite cardinality bound within each cluster system, positive annular density, and a prescribed countable family of moduli. It gives no avoidance theorem for arbitrary C1 maps, unbounded clusters, a continuous interval of candidates, all real powers, or all null moduli.

The audit-required correction replaces a false recurrence claim for maximizing windows of the original set by maximization in each translated tail. [The mathematical clarification patch](MATHEMATICAL_CLARIFICATIONS.patch) records that repair and the other audited clarifications. Original audited subjects are preserved in the shared provenance directory.

## Exact finite evidence

`verification/check_cluster_cover.py` uses rational half-plane clipping, retaining segments, singletons, and touching-open-interval gaps. Its assertion is: for every normalized parameter pair, there is one entire cluster whose closed uncertainty intervals all lie in the open holes. The cluster is chosen before the independent errors.

- Four-cluster certificate: open holes `(0,4/5)+Z`, relative error radius `a/100`, exact density `4/5`, nine polygon states
- Six-cluster certificate: `(0,3/4)+Z`, same relative error radius, exact density `3/4`, fourteen states
- Seven original regression cases
- Independent Fourier–Motzkin/arrangement oracle: 1,006 cases, 159 covers and 847 failures

These are normalized finite examples. They are not computed witnesses for every arbitrarily small density budget and do not computationally prove the infinite theorem.

Run `python3 ../avoidance-covering-provenance/verify.py` to replay all evidence in a temporary directory. Run `bash build.sh` to rebuild this PDF. The full source-complete two-note package also has one shared build script and an exact whitelist/hash manifest.
