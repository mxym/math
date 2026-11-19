# Two units of supply: the exact availability–throughput curve

Yongxian Zhang

Suppose a kitchen has two units of soup and $n\ge2$ diners. Their demands are independent; each may take **any** value between zero and one. Among all such populations with a fixed probability $q$ of having soup left, the least expected amount served is attained by $n$ identical, independent diners who each request **either zero or one**. They need not model the original diners: they give the sharp comparison.

To compute the minimum, solve $nz^{n-1}-(n-1)z^n=q$ for $z\in[0,1]$. The minimum absolute throughput is $2-q-z^n$; divide by two for the expected fraction served. For instance, with three diners and $q=1/2$, $z=1/2$. At least $11/8$ units are served on average, and three fair binary requests attain that value.

Letting the population size vary gives the sharp Poisson frontier: for $0<q<1$ solve $(1+\lambda)e^{-\lambda}=q$; the throughput infimum is $2-q-e^{-\lambda}$. Finite binomial populations approach it at the prescribed availability. At $q=0$ all soup is served; the Poisson endpoint is a limit, not a finite Poisson law.

[Proof](FINITE.md) · [Sources and scope](SOURCES.md) · [Independent internal review](REVIEW.md)

The proof uses only a pointwise comparison of the shortage before and after omitting one diner, followed by generalized Hölder. The original conjecture concerns all supplies; this paper proves the exact two-unit case only. The repository's [fractional-supply results](../soup-kitchen-fractional-supply/README.md) concern a different part of that question.

**Optional exact checks** (standard-library Python): run `sha256sum -c SHA256SUMS`, then `python3 -O check.py | diff - CHECKS.txt`. These checks exercise deterministic projection bounds, examples with unequal fractional demands and binomial cases attaining the frontier. No numerical root solving is needed.

AI-assisted research with independent AI-assisted internal review. No external peer review or guarantee of priority.
