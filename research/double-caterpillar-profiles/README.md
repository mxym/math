# Double-caterpillar upper boundaries: the cutoff at seven leaves

Brosch and Puges asked whether, at its particular density of the rooted caterpillar on $k$ leaves, every double caterpillar maximizes the density of the six-leaf shape $E_6$ with root split $3+3$. The answer is **yes for $k=4,5,6$ and no for every $k\ge7$**. This concerns leaves sampled in a growing rooted binary tree, not induced subgraphs on uniformly sampled vertices.

* **Positive range.** Join two caterpillars in proportions $p$ and $1-p$. For $k=4,5,6$ the resulting arc is the exact upper boundary wherever it is defined: the horizontal coordinate ranges from $(k+1)/2^{k-1}$ to $1$. This extends the original authors' certificates at the balanced double caterpillar, not their formulas for the arc itself.
* **Negative range.** For each fixed $k\ge7$ and every sufficiently small positive $p$, replace the smaller caterpillar by a pair of caterpillars, then tune its total mass. The new construction has **exactly the same limiting** caterpillar density but a strictly larger $E_6$ density. A new $3+3$ split contributes at order $p^6$; restoring the other density costs only order $p^k$. There is no claim about all $p$ for these $k$, the best competitor, the rest of the upper boundary, or the lower boundary.

[Proof and precise statements](PROOF.md) · [Primary sources and comparison](SOURCES.md) · [Internal mathematical review](REVIEW.md).

[The exact checker](check.py) compares direct leaf-subset enumeration and split counts, tests the sharp inequalities on rationally weighted skeletons, and certifies three strict rational inequalities for a $k=7$ example. Its two endpoints bracket the required mass by continuity: this is a counterexample at identical profile coordinates in the horizontal direction, not a comparison of two nearby coordinates or two exactly matched finite histograms. See [the recorded output](CHECKS.txt). The proof for every $k$ is analytic, not based on finite tests.

Run from this directory (Python 3.8+ and a SHA-256 checker):
```sh
sha256sum -c SHA256SUMS
python3 -BO check.py > replay.txt
diff -u CHECKS.txt replay.txt
```

This AI-assisted working paper received a separate internal AI mathematical review. It has not been externally peer reviewed or formally verified; no priority guarantee is made.
