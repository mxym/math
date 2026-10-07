# Simultaneous integer-degree failures of harmonic dimension comparison

This note records a quantitative strengthening of the three-dimensional
counterexamples in OpenAI/math family 361.

The upstream theorem constructs, for each sufficiently large integer degree
k, a complete smooth metric on R^3 with nonnegative Ricci curvature and more
polynomial-growth harmonic functions of degree at most k than Euclidean
space. Its near-Euclidean version allows the multiplicative excess at degree
k to approach 9/4.

The observation here is that polynomial-growth spaces are monotone in the
degree. Combining that fact with the full upstream quantitative constant
yields a **simultaneous block theorem**: one and the same metric violates
the Euclidean dimension comparison at every integer degree in a
multiplicative interval whose endpoint/start ratio can be any number below
3/2. More quantitatively, if beta > 1 and A > 1 satisfy

    A beta^2 < 9/4,

then the same metric gives an A-factor excess throughout the block.

Files:

- [paper.md](paper.md): complete statement and proof;
- [PROOF_AUDIT.md](PROOF_AUDIT.md): dependency-by-dependency audit;
- [checker.py](checker.py): exact-rational replay of the finite inequality;
- [SOURCE_MAP.md](SOURCE_MAP.md): pinned upstream dependency.

This is an additive consequence of the upstream theorem, not a new proof of
its analytic construction. In particular it does **not** produce one fixed
metric violating the comparison at infinitely many unbounded degrees. That
stronger quantifier reversal remains separate.

No novelty or priority claim is made.
