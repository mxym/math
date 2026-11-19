# Sharp positive weak-Mallows asymptotics with bounded decreasing subsequences

Fix a positive real $\beta$ and positive integer $d$. Give each permutation of $[n]$ avoiding the decreasing pattern of length $d+1$ weight $e^{\beta\operatorname{inv}/n}$. This note determines the full leading equivalent for the **uncoloured** total weight, not just its exponential rate. If $F=2(G(1)-dG(1/d))$, $G(x)=\int_0^x\log a(y)dy$, $a(y)=2\sinh(\beta y/2)$ and $H=(\beta/2)\coth(\beta/(2d))$, then
$$Z_{n,d}(\beta)\sim e^{nF} n^{-(d-1)/2}
\left(\frac{\beta}{2\pi}\right)^{d-1}\left(\frac{\pi}{H}\right)^{(d-1)/2}
\frac{a(1)}{\sqrt d\,a(1/d)^d}
\prod_{h=1}^{d-1}(1-e^{-\beta h/d})^{2(d-h)}.$$
The last product corrects the count of *all* equal-content word pairs to that of genuine canonical permutations. A corresponding multivariate CLT holds for canonical layer sizes about $(n/d,\ldots,n/d)$ on scale $\sqrt n$: their limiting covariance is $(2H)^{-1}(I-\mathbf1\mathbf1^\top/d)$.

- [Partition asymptotics and CLT](PREFACTOR.md): a uniform estimate over the interior and both boundary regimes reduces the correction to two independent infinite-end survival probabilities.
- [Explicit survival probability](TRANSMISSION.md): the Denisov–FitzGerald determinant for ordered exponential walks is verified for the asynchronous compound-Poisson kernel coming from these words.
- [Scope and prior results](SOURCES.md): the free energy itself, the canonical representation and the chamber determinant are prior ingredients. The result is not uniform down to zero bias, for increasing $d$, or for other forbidden patterns.
- [Internal proof review](REVIEW.md), [transmission review](TRANSMISSION-REVIEW.md), [finite checker](check.py), [expected output](CHECKS.txt).

Run `python3 -O check.py` and `sha256sum -c SHA256SUMS`. The combinatorial/rational checks are exact; the final four ratios use a floating forward evaluation of an exact width-two transfer, as a diagnostic only. AI-assisted mathematical development and a separate internal AI proof review, not external peer review or a guarantee of novelty.
