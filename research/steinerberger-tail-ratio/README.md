# Exponential laws are not extremal for Steinerberger’s mean–minimum tail questions

**Yongxian Zhang (张永贤) · Research draft · November 19, 2026.** AI-assisted, with independent internal mathematical reviews; not externally peer reviewed.

[Steinerberger's open-problem list, §24, Questions 1 and 2](https://faculty.washington.edu/steinerb/openproblems.pdf#page=26), asks whether every unbounded continuous law, at some positive threshold, matches the tail comparison attained by an exponential law. The two questions normalize the threshold by the median or mean, respectively.

**Neither exponential benchmark works. Smaller universal constants do.** Both results concern independent samples $X,Y$ from the same absolutely continuous law on $[0,\infty)$. For $t>0$ let $G(t)$ be the ratio, among pairs with $X+Y\ge2t$, of the probability that one sample is below $t$ to the probability that both are above $t$. Equality events have probability zero.

* **[One counterexample to both proposed constants](PROOF.md).** Use the classical linear-failure-rate family with survival $S(t)=e^{-5t-t^2/2}$. Direct integration proves that $G(t)/t\le 283/28$ everywhere, strictly below *both* exponential benchmarks $2\log(2)/\mathrm{med}(X)$ and $2/\mathbb EX$ for this law. The density is smooth and strictly positive on the half-line; the mean is finite.
* **[Positive constants for the existential question](UNIVERSAL.md).** For every such law with unbounded support, some $0<t\le2\,\mathrm{med}(X)$ satisfies $G(t)>1/24$. At that same threshold $G(t)>t/(48\,\mathrm{med}(X))$, and $G(t)>t/(96\,\mathbb EX)$ whenever the mean exists. These constants are not asserted to be sharp, and existence of one such threshold is not linear growth at infinity.

[Sources and distinctions from earlier results](SOURCES.md) · Independent internal reviews: [counterexample](REVIEW.md) and [positive bound](UNIVERSAL-REVIEW.md). Neither proof requires numerical computation. For an optional exact arithmetic replay, run `python3 -O verify.py` and compare with [CHECKS.txt](CHECKS.txt); `sha256sum -c SHA256SUMS` verifies file integrity. No historical-priority guarantee is made.
