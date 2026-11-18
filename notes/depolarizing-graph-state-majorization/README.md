# Product-reference majorization for noisy graph states

For a weighted graph state over the cyclic alphabet $\mathbb Z_d$, independent local depolarizing noise produces an output whose spectrum is majorized by that of the same noise on a pure product input. This holds for every number of sites and for unequal noise strengths throughout their physical ranges, even when some channel contractions are negative. The comparison also holds on the convex hull of local-unitary images of these graph states; at prime local dimension this includes pure stabilizer states and their mixtures.

The proof turns each error into a shift of a graph-basis label. Conditional on part of the error, compressing a set of labels one coordinate at a time can only increase its probability. A related calculation handles **correlated erasures** on graph states, not arbitrary correlated noise.

* [Theorem, proof and scope](PROOF.md).
* [Prior work, attribution and internal checks](REVIEW.md). The two-use and three-qubit all-input cases are consequences of earlier work, **not new claims**. Related Weyl-channel theorems mean that priority for the graph-state formulation has not been established.
* [Independent exact checker](check.py): run `python3 -B -O check.py` with Python 3.10+ and SymPy 1.14. No numerical tolerances are used to accept a majorization inequality.

This is an AI-assisted research draft with independent internal AI checking, not external peer review. It does **not** prove the [general depolarizing-output conjecture (Eq. 2)](https://arxiv.org/html/2609.37240v2), determine its validity on all states, or claim the first result for this subclass.
