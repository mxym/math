# Exactly when a fixed i.i.d. cost law has a bounded prophet ratio

**Yongxian Zhang · 19 November 2026.** AI-assisted manuscript with independent internal AI review, not external peer review. No priority guarantee.

An online decision maker must take exactly one of $n$ i.i.d. costs; a prophet pays their minimum. Fix the known, nonnegative law once, with positive finite mean. [Earlier counterexamples](../fixed-law-min-prophet-counterexample/) show that boundedness of the optimal online-to-prophet expected-cost ratio does not follow even from bounded continuous support. This note gives a **necessary and sufficient test using the distribution function, without running the stopping recursion**.

* If the essential lower endpoint is positive, the ratio tends to one.
* If that endpoint is zero but zero has no mass, choose $c>0$ with $0<F(c)<1$. Put $D(x)=\int_0^xF(t)dt$, $L(s)=-\log(1-s)/s$ with $L(0)=1$, and $T(x)=\int_x^c dt/[D(t)L(F(t))]$. Then the optimal online cost is asymptotic to $T^{-1}(n)$. The exact limiting upper ratio is the reciprocal of
  $$
  \liminf_{x\downarrow0}\frac{1}{x}\int_0^c (1-F(t))^{T(x)}\,dt .
  $$
  Thus the ratio is bounded precisely when this quantity is positive, whatever the behavior of the upper tail. Atoms at positive costs are allowed.
* If zero has positive mass, the test is especially simple: the ratio is bounded **exactly when the positive costs are bounded away from zero**. Otherwise it diverges along the entire sequence of horizons.

The smooth expression behind $T$ is the known Buff differential. The proof bounds its one-step error by the change of a monotone function, so the errors sum to a bounded quantity even for discontinuous distribution functions. The test is an integral criterion on a whole lower tail, not a finite-moment test or a constant uniform over all laws.

[Proof](PROOF.md) · [Independent internal review](REVIEW.md) · [Sources and comparison](SOURCES.md).

Run `python3 -B -O check.py` and compare with [the recorded checks](CHECKS.txt). It certifies 240 one-step clock estimates using rational bounds on logarithms and checks two contrasting examples with a zero atom. The analytic proof stands without these finite tests. File digests: `sha256sum -c SHA256SUMS`.
