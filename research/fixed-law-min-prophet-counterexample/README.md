# A bounded fixed-law counterexample for the i.i.d. cost prophet inequality

**Yongxian Zhang · 19 November 2026.** AI-assisted research note with independent internal AI proof review; no external peer review or claim of priority.

An online decision maker observes independent draws from a known cost distribution and must take one; the prophet takes the cheapest draw. Does finite mean guarantee that the two expected costs are within a constant factor once the distribution is fixed? **No, even for a continuous distribution on the unit interval.** This concerns the positive finite-mean assertion of [Livanos and Mehta, SODA 2024, Theorems 1.1 and 3.1](https://par.nsf.gov/servlets/purl/10511091), as printed, rather than the narrower positive results in the 2023 preprint or the subsequent extreme-value-domain paper.

Write $G_n$ for the optimal online expected cost and $M_n$ for the expected minimum. [The main proof](PROOF.md) gives an explicit law with survival $\exp(-1/\log(1/x))$ on $0<x<1$ and shows
$$
\log(G_n/M_n)=(2-\sqrt{2}+o(1))\sqrt n.
$$
Thus the cost ratio grows along the entire sequence of horizons, not just for a different hard instance at each horizon. The same construction with a positive power of the logarithm gives every exponent strictly between zero and one, with explicit leading constant. The proof also identifies the failed order-statistic comparison in the formal paper and verifies why the example is outside the later extreme-value hypotheses.

[The envelope theorem](ENVELOPE.md) makes the order of the quantifiers precise. For every fixed nonnegative integrable law not identically zero, $\log(G_n/M_n)=o(n)$. But for every proposed nonnegative $h(n)=o(n)$, some **single bounded atomless law** beats $j\max(1,h(n_j))$ at increasing horizons $n_j$. That law may depend on $h$. This does not give an exponential-in-$n$ ratio for a fixed law. The three-level mechanism for a law that **changes** with the horizon goes back to Esfandiari, Hajiaghayi, Liaghat and Monemizadeh.

[Source comparison](SOURCES.md) · Independent reviews: [main proof](REVIEW.md), [envelope](ENVELOPE-REVIEW.md).

### Reproduce the finite checks

Run `python3 -B -O check.py` from this directory. [Expected output](CHECKS.txt) includes a certified ratio above 10,000,000 at $n=4096$ for the first continuous law, exact order-statistic identities by enumeration and four three-level Bellman checks. These illustrate the analytic proofs; the asymptotic results do not rest on a simulation or a finite search. Run `sha256sum -c SHA256SUMS` for the file digests.
