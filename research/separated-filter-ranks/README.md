# Interior cross-product inequalities from separated filter ranks

Fix a finite poset and distinct marked elements x,y,z. Write F(k,l) for the number of linear extensions in which the two successive rank gaps are k,l≥1. Impose x<y<z, without changing these counts. Among the elements incomparable with y, form the graph with an edge between two points precisely when they are incomparable. Let Δ be the maximum vertex degree of this graph (not its maximum clique size). Put Δ=0 for the empty graph.

For arbitrary positive k,l and positive increments r,s≥Δ, we prove

    F(k,l) F(k+r,l+s) ≤ F(k+r,l) F(k,l+s).

Thus the classical **adjacent-cell** inequality is established at every positive location whenever Δ≤1, not only at a minimum feasible gap. This includes every width-two poset, where the result is already known, and posets of unbounded width outside the middle incomparable set. For larger Δ the theorem covers rectangles whose increments meet the bound, not arbitrary adjacent cells.

The [proof](PROOF.md) derives a rank-count comparison for two filters, with a sharp sufficient spacing for that filter statement. In particular the marked rank shifts upward in likelihood-ratio order when passing from a smaller filter to a larger one. The proof uses the [earlier compulsory-anchor lemma](https://github.com/mxym/math/blob/37109641b5a68ea627f77cc67bc5d0a29da50a05/research/anchored-poset-cross-products/SHIFTED.md). [Sources and scope](SOURCES.md) · [Independent internal review](REVIEW.md).

Run, with Python's standard library:

```sh
python3 verify.py
python3 interior_samples.py
sha256sum -c SHA256SUMS
```

The first script exhausts naturally labelled posets through five points. The second checks genuine interior and wide rectangles via exact extension counting on larger examples. See [small checks](CHECKS.txt) and [larger checks](INTERIOR-CHECKS.txt). Neither finite computation replaces the proof. AI-assisted, internally checked, not externally refereed; no priority guarantee.
