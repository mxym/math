# A weighted average versus the minimum of two independent random variables

**Yongxian Zhang (张永贤) · Research draft · November 19, 2026.** AI-assisted, with a separate internal mathematical review; not externally peer reviewed.

Suppose two independent, nonnegative random quantities can each be arbitrarily large. Given that a fixed weighted average exceeds a high threshold, must *both* quantities typically exceed the threshold? **No:** at some arbitrarily high thresholds the conditional probability that they both do so is arbitrarily small. The two distributions can be entirely different and can have atoms. The weights can be any fixed positive pair summing to one.

This gives an affirmative answer to [Feldheim and Feldheim, §1.1, Conjecture 1](https://arxiv.org/pdf/1609.03004). Their Theorem 1 answered Alon's question for equal weights, with possibly different laws; their Theorem 2 allowed arbitrary weights for identical laws. The missing combination is unequal weights and independent nonidentically distributed inputs.

The [proof](PROOF.md) assumes the quotient of the weighted-mean tail by the product of the two individual tails stays bounded. On suitably tilted intervals this gives both a uniform *upper* bound on an area and a supply of separated points forcing the same area to be arbitrarily large. The theorem is a limit superior statement: it gives neither divergence at every threshold nor a prescribed rate.

Two implications already identified by the original authors are made explicit: [finitely many positive weights](PROOF.md#5-multiple-positive-weights) and [every norm in dimension at least two](NORM.md). In dimension one the norm ratio is identically one.

[Sources and scope](SOURCES.md) · [Independent internal review](REVIEW.md). For optional finite checks of the hull, interpolation and clipping, run `python3 -O verify.py` using only Python's standard library; compare with [the expected output](CHECKS.txt). These checks do not replace the proof for arbitrary laws. `sha256sum -c SHA256SUMS` verifies the files.
