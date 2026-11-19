# Comparable arcs matter for linear-extension majority cycles

For a uniformly random linear extension of a finite poset, draw x→y when x precedes y with probability strictly greater than one half. Does discarding the arcs between comparable vertices preserve the lengths of directed simple cycles? [Gupta's Question 14](https://arxiv.org/html/2607.23926v2#S8) asks this after an exhaustive positive check through 14 elements.

**No.** Take three disjoint chains of lengths 28, 5, and 10,000. The full majority graph has a four-cycle; the restricted graph cannot, since its four vertices would have to be an antichain. Four is the first possible length of disagreement. Width three is also the least possible width for a counterexample, though no minimum poset order is asserted.

The same three-chain construction gives an unbounded difference: as the third chain grows, the full graph realizes every simple-cycle length from 3 up to a bound linear in its length, while the restricted graph has no simple cycle longer than 66. At third-chain length 1,000,000, the full graph already has all lengths from 3 through 83.

- [Proof and exact shuffle formulas](PROOF.md)
- [Literature and scope](SOURCES.md)
- [Independent internal proof review](REVIEW.md)

Reproduce with `python3 -O verify.py` (Python standard library), compare the output with [CHECKS.txt](CHECKS.txt), and verify the package with `sha256sum -c SHA256SUMS`.

This AI-assisted note is about cycle lengths, not the 1/3–2/3 or Gold Partition conjectures. It has undergone internal mathematical review, not external peer review; priority is not asserted.
