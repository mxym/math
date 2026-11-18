# How fast do Schatten–Hlawka constants grow?

The triangle deficit measures how much norm is lost on adding matrices. Audenaert and Kittaneh ask how large the loss for three matrices can be compared with the sum of their three pairwise losses. Let $C_p$ be the best comparison constant for all finite rectangular complex matrices in the Schatten $p$-norm, and let $K_p$ be the constant for complex diagonal matrices only.

* **All matrices.** For $1<p<\infty$, we obtain $C_p\le 2\max(p,p/(p-1))$. Combined with Esa’s diagonal lower-bound family, this gives $C_p=\Theta(p)$ as $p\to\infty$. The upper bound controls a sum of any finite number of matrices by the sum of all pairwise losses, independently of that number. The proof makes Esa’s Bregman-to-Hilbert comparison quantitative.
* **Diagonal matrices.** Write $L=\log 2$. Using Esa’s exact variational formula, we obtain
  $$
  K_p=\frac{p}{3L}-\frac{\log p}{6L}+\frac{\log L+2L-\log 3-1}{6L}
      +O\!\left(\frac{(\log p)^2}{p}\right).
  $$
  The maximizing parameter in Esa’s cyclic family is unique for sufficiently large $p$, with $t_p^p=L/p+O((\log p)/p^2)$.

Esa’s existence theorem, transfer method, diagonal variational formula, and test family giving the leading lower slope **precede this note**. The logarithmic-scale lower correction was also visible in earlier witness estimates. We do not identify the unrestricted leading coefficient, determine the sharp constant for arbitrary matrices, show that the worst case is diagonal, classify all extremizers or settle the behavior near $p=1$.

Read the [proof](PROOF.md), [prior work and references](SOURCES.md), and [verification and review notes](CHECKS.md). AI-assisted research draft with a separate internal mathematical review, not an external peer-reviewed result. The arguments in this note are not formally verified; no worldwide priority claim is made.
