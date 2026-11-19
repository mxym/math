# When does the expected count of independent sets describe a typical Cayley tree?

Choose a labeled tree uniformly on $[n]$. Let $X$ be its number of independent sets having exactly $k$ vertices, and divide by the classical exact expectation:
$$Y=\frac{X}{\binom{n}{k}(1-k/n)^{k-1}}.$$
The transition occurs when $k$ is of order $n^{5/6}$. For each sequence of integers $1\le k=k(n)\le n-1$:

* **Below:** if $k=o(n^{5/6})$, then $Y\to 1$ in mean square.
* **At the transition:** if $k/n^{5/6}\to t\in(0,\infty)$, then $Y$ converges in distribution to $\exp(sZ-s^2/2)$, where $s=t^3/\sqrt2$ and $Z$ is standard normal. Its second moment converges to $\exp(s^2)$.
* **Above:** if $k/n^{5/6}\to\infty$, then $Y\to0$ in probability and its second moment diverges, even for $k$ approaching $n-1$. This says that the expected count is atypically large, not that the typical count vanishes.

Relative to the **path count**, the scale is different: if $k/n^{2/3}\to u\ge0$ is finite, then $X/\binom{n-k+1}{k}\to e^{u^3/2}$ in mean square. This is not the [macroscopic exponential improvement over the path](../cayley-tree-path-coefficient-gap/).

The [proof](PROOF.md) couples a second-moment calculation to a statistic observable from the tree alone: the number of pairs of equal labels in its Prüfer code. In the model with a planted independent set, this statistic shifts by exactly the amount needed to determine the critical law. See the [prior work and scope](SOURCES.md), [internal review](REVIEW.md), and [independent derivation](DERIVATION.md). The statements are sequence by sequence, not simultaneous control of an entire random coefficient profile. No sharp decay rate above the transition, higher lognormal moments, or historical priority is asserted.

## Verification

From this directory, using Python 3 (standard library only) and a shell with pipefail:

~~~sh
set -eo pipefail
sha256sum -c SHA256SUMS
python -B -O check.py | diff - AUTHOR-CHECKS.txt
python -B -O independent.py | diff - CHECKS.txt
~~~

The first program uses exact spanning-tree cofactors and occupancy identities. The second directly enumerates all 18,248 labeled trees of orders 2 through 7 and reconstructs full planted degree polynomials. These finite checks complement, and do not establish, the probability limits. This is AI-assisted mathematics with independent internal AI derivations and review; it has not undergone external peer review.
