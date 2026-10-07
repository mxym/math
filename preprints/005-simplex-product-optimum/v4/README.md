# Symmetric equality classification for the projection-cone invariant

**Entry 005, version 4 — 7 October 2026. Complete written proof draft; exact rational regressions.**

Read the [manuscript](paper.md), [proof audit](PROOF_AUDIT.md), and [exact regression script](code/check_examples.py).

## New theorem

For every full-dimensional centrally symmetric convex body \(K\subset\mathbb R^d\),
\[
a(K)=\frac12
\]
if and only if \(K\) is affinely equivalent to a Cartesian product
\[
K_1\times\cdots\times K_m
\]
whose factors are centrally symmetric and have dimensions one or two.

This closes the higher-dimensional equality question explicitly left open in version 3. In dimension three the equality bodies are exactly affine prisms over centrally symmetric planar bodies. In dimensions at least three, every affinely indecomposable, strictly convex, or \(C^1\)-smooth centrally symmetric body satisfies the strict inequality \(a(K)<1/2\). A dimensionwise qualitative stability theorem also shows that \(a(K)\) close to \(1/2\) forces Banach--Mazur closeness to this product equality class.

## Proof mechanism

The proof has four structural steps.

1. The balanced Rademacher inequality used in version 3 is given a complete equality classification.
2. Cone-volume laws are shown to be concentrated on exposed points of the polar body; exposedness eliminates the otherwise possible four-or-more-point equality circuits.
3. An almost-sure cofactor-support condition is converted by a Fubini/matroid argument into a direct-sum decomposition into one- and two-dimensional normal blocks.
4. A mixed-volume argument shows that a convex body whose surface-area measure is supported on those blocks is exactly the Cartesian product of its block projections.

The exposed-point step is essential: an explicit even boundary law on the three-dimensional \(\ell_1\)-ball attains the random-determinant equality through a four-point circuit containing a non-extreme boundary point.

## Exact replay

Python 3.10 or newer; standard library only:

\`\`\`sh
python3 code/check_examples.py
\`\`\`

The script uses \`fractions.Fraction\` throughout. It verifies:

- 7,749 balanced rational Rademacher tests (2--6 coefficients, denominators through 10), including a complete finite check of the equality criterion on that grid;
- the strict four-equal-coefficient Rademacher value \(3/8\);
- the half-mass equality mechanism;
- the non-extreme boundary-law example \(A=3/16,\ B=3/8\);
- the three-dimensional coordinate-axis equality law \(A=2/9,\ B=4/9\);
- the cube-vertex strict benchmark \(A=3/2,\ B=45/16\), giving \(a=15/32\).

These finite computations are regression tests. The general classification is proved in the manuscript.

## Scope

Version 4 inherits the invariant calculus, cone-volume representation, symmetric inequality, planar equality theorem, and exact product identity from versions 2--3. It does not determine the quantitative stability gap below \(1/2\), nor the recursive spectral supremum \(\lambda_*\).

No first-discovery or best-known claim is made before a focused literature comparison.
