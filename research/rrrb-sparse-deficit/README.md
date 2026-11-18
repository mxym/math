# How fast does the sparse RRRB profile approach its limit?

Let $M(p)$ be the supremum of the probability that four labelled vertices in a graphon span red edges $12,23,34$ and a blue edge $41$, at red-edge density $p$. The diagonals have no prescribed colours. As $p$ decreases to zero,
$$
\frac12-\frac{M(p)}{p^2}
=\Theta\!\left(\frac{1}{\log(1/p)}\right).
$$
The leading constant $1/2$ is already a consequence of the edge-inducibility theorem for the paw of [Chao, Cohen Antonir, Li and Yu](https://arxiv.org/abs/2509.24064). The issue here is the **size of the deficit**. The upper estimate for $M$ holds for every graphon; a sequence of ordered step constructions, diluted to any desired small red density, matches its order.

There is also a matching complexity bound: a graphon with at most $s$ classes has deficit at least $1/(4s)$. Achieving deficit $O(1/\log(1/p))$ therefore requires $\Omega(\log(1/p))$ classes, and that order suffices. This concerns families achieving the asymptotic order, not exact optimizers at individual densities.

[Proof and constants](PROOF.md) · [Step complexity](STEPS.md) · [Prior work and checks](REVIEW.md). The graphon limit is taken at fixed red density before $p\downarrow0$. This note does not determine a sharp coefficient, a finite-$p$ exact optimum in the sparse range, or a simultaneous limit in vertex count and density. It is separate from the [dense-range profile](../rrrb-lower-saturation/README.md) and the [alternating cycle](../alternating-four-cycle-fixed-density/README.md). AI-assisted research with independent internal AI review; no external peer review or priority claim.
