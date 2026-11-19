# A square-root upper window for the mode on a random labeled tree

Let $T_n$ be a uniform tree on $[n]$. First sample the tree; then, conditional on that tree, draw an independent set $I$ uniformly, including the empty set. Define $A(T_n)=\mathbb E[|I|\mid T_n]$. Let $\mathcal M(T_n)$ be **all** maximizing indices of the independent-set coefficients of the sampled tree. The centering constant $\mu$ is the deterministic occupancy density from [the preceding result](../PROOF.md), not a mean chosen separately for each tree.

The [proof](PROOF.md) gives
$$
\mathbb EA(T_n)=\mu n+O(1),\qquad
\operatorname{Var}_{T_n} A(T_n)=O(n),\qquad
\mathbb E\max_{m\in\mathcal M(T_n)}|m-\mu n|^2=O(n).
$$
Thus all modes lie in an $O_{\mathbb P}(\sqrt n)$ window around the same deterministic center. This is an upper scale, not a matching lower bound, limiting distribution, or fixed-constant window holding with probability tending to one. The new variance bound is over the choice of tree, not the variance of $|I|$ given one tree.

The proof compares finite labeled trees with one and two independent Kesten neighborhoods and controls the boundary error of a root occupation. It uses existing stabilization and moment estimates in spirit and the established within-tree mode/mean estimates explicitly. See [source boundaries](SOURCES.md) and the [separate AI review](REVIEW.md). This is AI-assisted research, internally checked but not externally peer-reviewed, with no assurance of priority.

To reproduce the finite counts, from this directory run:

~~~sh
sha256sum -c SHA256SUMS
python -B -O sqrt_check.py | diff - AUTHOR-CHECKS.txt
python -B -O independent.py | diff - CHECKS.txt
~~~

The two standard-library programs use different enumeration methods. They check finite identities, not the asymptotic conclusion.
