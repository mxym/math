# Smooth distributions with prefix-optimal finite-state generators

**Yongxian Zhang.** AI-assisted research draft; independently checked within the AI workflow, not externally peer-reviewed.

One fair-coin-driven finite graph generates the entire binary expansion of a random real in [0,1]. An edge may print any fixed finite string, including the empty string. If only the first $n$ digits were required, their discrete law would have a minimum expected coin cost $C_n$. When can the *same* graph attain $C_n$ for every $n$?

For a smooth distribution function $F$ with $F(0)=0$ and $F(1)=1$, this is possible **exactly** for
$$F(x)=(1-r)x+rx^2,\qquad r\in\{0\}\cup\{\pm 2^{-s}:s=0,1,2,\ldots\}.$$
Thus even $F(x)=x^3$, which is known to have an exact finite generator, has none that is optimal at every precision. The [classification proof](PROOF.md) first uses finite-state recognition to rule out nonlinear densities, then isolates the allowable slopes and constructs all the surviving generators. It does not classify nonsmooth laws.

For the cubic law, let $M_*(\varepsilon)$ be the least number of original graph states permitting an **exact** sample with $\mathbb E T_n\le C_n+\varepsilon$ simultaneously for every $n$. We prove
$$\Omega(\log(1/\varepsilon))\ \le\ M_*(\varepsilon)\ \le\ O(\varepsilon^{-6})$$
as $\varepsilon\downarrow0$. The [quantitative proof](CUBIC.md) counts original states even when an edge emits several bits. The bounds do **not** determine the sharp growth rate. The approximation is in cumulative expected coin cost, not in the law or the cost per bit.

[Draper and Saad, §9](https://arxiv.org/pdf/2607.14503v1), revisit this question and distinguish it from per-sample loss. [Kindler and Romik](https://doi.org/10.1137/S089548010343106X) already classified smooth laws that can be generated without the optimality requirement. See [sources and historical limitations](SOURCES.md) for the precise comparison to Knuth and Yao, Pokhodzeĭ and other prior work. No worldwide priority claim is made.

**Replay.** Run `python3 -O check.py` and compare to [CHECKS.txt](CHECKS.txt); use `sha256sum -c SHA256SUMS` to verify the files. The arithmetic checks test finite instances, not the infinite statements. The independent internal reviews of the [classification](REVIEW.md) and the [cubic bounds](CUBIC-REVIEW.md) identify the exact proof files reviewed.
