# A strong Chollet inequality for simple graph Laplacians

For every finite simple unweighted undirected graph G, with Laplacian L, and every vertex subset S, the complete proof establishes

$$\operatorname{per}(L[S]\circ L[S])\leq\operatorname{per}(L[S])\prod_{v\in S}\deg_G(v).$$

In particular,

$$\operatorname{per}(L\circ L)\leq\operatorname{per}(L)\prod_v\deg_G(v)\leq\operatorname{per}(L)^2.$$

This answers the two all-graph questions in Section 6 of [Pant and Singh, arXiv:2604.24192v2](https://arxiv.org/html/2604.24192v2). The result concerns simple graph Laplacians; it does not settle Chollet's conjecture for arbitrary Hermitian positive semidefinite matrices, nor claim the weighted-graph version.

## Proof

[Read the complete proof](proof.txt).

The main argument constructs the fractional matching x(uv) = 9/(5 deg(u) deg(v)) in every 2-connected noncycle block. Edmonds' matching-polytope theorem and Lieb's block permanent inequality provide a logarithmic lower bound with coefficient 8/5. A directed-cycle expansion provides an upper bound with coefficient 19/12. Their positive difference, 1/60, proves the strong inequality on every principal submatrix of such a block. Cycle blocks and hereditary closure under vertex coalescence complete the all-graph proof.

Lieb's theorem and Edmonds' theorem are standard external dependencies, stated explicitly in the proof. The one-point-sum closure is attributed to Pant and Singh and reproduced with its full argument.

## Verification and status

The proof was developed with AI assistance and received an independent AI mathematical audit of its full quantified argument. That audit reported no mathematical gap. This is not human peer review or a complete Lean formalization, and no absolute priority claim is made.

The proof does not use numerical experiments as premises. The optional [dependency-free Python diagnostic](verify.py) checks exact integer and rational consequences on a bounded collection of graphs, including all labeled simple graphs through order five and selected larger boundary cases. Its [recorded output](diagnostics.json) contains 35,466 principal-submatrix checks and 3,784 odd-set matching-polytope checks. These finite tests supplement the general proof and do not replace it.

Run the diagnostics with Python 3.10 or newer:

```sh
python verify.py
```

[Source and scope record](sources.md) · [SHA-256 manifest](manifest.json)
