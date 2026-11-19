# The sharp largest atom for a sum of three integer random variables

**Yongxian Zhang · working paper · 19 November 2026.** AI-assisted mathematical research with a separate AI-assisted internal proof review; not externally peer-reviewed. No global priority claim.

Given three independent integer-valued variables and a different upper bound on the mass of each one's largest atom, how large can a single atom of their sum be? This note gives the exact answer for **every triple of caps**. An optimizer puts as many atoms as possible at the cap on consecutive integers and any residual mass at one end; the choice of left or right can differ between variables.

This proves the three-summand case of [Juškevičius's conjecture as formulated by Kurauskas, Conjecture 1.3](https://arxiv.org/pdf/2603.11043v1). The caps need not be reciprocal integers, equal or large. This is about the mass **at one integer**, not in an interval; it is not a solution for an arbitrary number of summands.

The [proof](PROOF.md) gives the optimum by one eight-term expression. Each term comes from a uniform box of three possibly different side lengths. Individually optimizing all eight boxes would overestimate the answer: in the critical case one of the four boxes having an integer center must lose at least one representation. A signed interval construction can sacrifice precisely the least expensive such box. The proof treats singleton supports and zero residual masses explicitly.

[Sources and prior results](SOURCES.md) · [independent internal mathematical review](REVIEW.md). The proof is not computer-assisted. Exact arithmetic tests independently compare its formula with direct convolution and a finite exhaustive search over noninterval placements.

~~~sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
~~~
