# Maximum spread of realizable binomial bases cannot decrease with the number of bits

**Yongxian Zhang · 19 November 2026 · Research draft.** AI-assisted; independently reviewed internally, not externally peer reviewed. No global-priority claim.

For fixed even $k$, consider the extremal problem of maximizing the probability that all $n$ equal-marginal, $k$-wise independent bits are one. A *realizable basis* is optimal over a positive-length interval of the common success probability $p$. Its *spread* is the distance from the smallest to the largest count in the basis after omitting the distinguished count $n$. Write $\operatorname{Msp}(n,k)$ for the largest such spread.

The [proof](MONOTONE.md) gives $\operatorname{Msp}(n+1,k)\ge\operatorname{Msp}(n,k)$ for every even $2\le k\le n-1$. This answers [Berend–Ernst–Kontorovich–Kumar, Conjecture 5.12](https://link.springer.com/article/10.1007/s10959-026-01487-4) in its stated domain. The two realizations need not have the same $p$, and a support feasible only at an isolated parameter is not counted.

A sign certificate made from the outermost pair of an old phase remains positive under binomial degree elevation. It forces a realizable phase for one more bit whose support reaches at least as far in both directions. The [earlier exact four-wise formula](../k-wise-binomial-optimal-bases/FOUR.md) already implies monotonicity at $k=4$; the earlier [general asymptotic estimate](../k-wise-binomial-optimal-bases/SPREAD.md) does not imply one-step monotonicity. There is no new all-order closed form for the maximum or result on exceptional-parameter rationality here.

[Sources and exact scope](SOURCES.md) · [Independent internal mathematics review](MONOTONE-REVIEW.md). The finite check exhausts 4,111 paired bases, identifies 771 positive-length occurrences, and recovers the small-$n$ maxima without relying on the monotonicity theorem.

```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```
