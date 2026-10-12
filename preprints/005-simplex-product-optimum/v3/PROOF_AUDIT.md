# Proof audit — 005 v3

**Model-conducted self-audit, 7 October 2026.** This is not external human review or proof-assistant formalization.

## Written proof obligations

1. The random-law theorem assumes a finite first moment, zero mean and full linear span. Independence gives finite determinant expectations. Centering implies full affine span and a finite positive circuit; compact support is not silently assumed.
2. Conditional Jensen is used before integrating over all ordered horizontal tuples, including singular ones. Continuity of its nonnegative defect promotes almost-everywhere equality to every support tuple. Neighborhoods of support points have positive measure, including when the law has no atoms.
3. Minimal positive circuits have horizontal rank one below their cardinality and independent lifts. A circuit of size at most $d$ creates a horizontally singular tuple with a nonzero lifted extension. This excludes that case without dividing by a zero determinant.
4. A circuit of size $d+1$ supplies an enclosing simplex. Any additional support point has two positive barycentric coordinates; omitting those two vertices and inserting that point produces opposite nonzero determinant signs. Boundary and interior additional points are both covered.
5. Strictness of the upper triangle bound uses a repeated support point and continuity on product neighborhoods, not the probability of exact repetition. The center-atom mixtures give the sharp supremum but are not claimed to be cone-volume laws.
6. The cone-volume pushforward is centered, compactly supported and spanning. The polytopal factorial normalizations give $a=B/((d+1)A)$. Weak continuity of surface area measures and uniform support-function bounds pass this identity to every convex body.
7. General equality is not obtained by taking a limit of polytopal equality statements. The probability theorem gives $d+1$ supported normals; first variation and Brunn--Minkowski force equality of the body with the enclosing simplex.
8. Maximum-simplex normalization bounds every barycentric coordinate in absolute value by one. Compactness preserves nondegeneracy and maximum inscribed simplex volume, proving a uniform qualitative affine modulus. No effective estimate for that modulus is implied.
9. The symmetric upper bound requires support on the boundary of a common symmetric convex body, not merely an even law. Cofactor dependence and the Minkowski norm give balanced coefficients; independent sign averaging and the elementary capped-simplex convexity argument yield the constant $1/2$. The planar equality calculation and octahedron strict case are separate.
10. Spectral improvement compares $\lambda$, not $R^{1/d}$. With $N=k(d+1)-1$, the exact gain is $(k\lambda/a)\binom{2N}{N}/4^N$. The sufficient threshold is non-strict but the conclusion is strict because $N<k(d+1)$. The binomial induction covers $N=1$. No Stirling approximation or oracle is needed.

## Independent finite arithmetic

The producer uses unordered subsets and rational elimination. The checker independently uses ordered tuples and the Leibniz formula, reconstructs the complete cancellation defect, verifies centering, support rank, equality flags, certified norm slabs and sign witnesses. Spectral values are checked by a different central-binomial formula and integer-power comparisons. The octahedron is also checked directly from facet data. Neither script imports the other.

The complete replay verifies 23 laws and 18,199 ordered lifted tuples, 1,149 balanced sign lists, five spectral recipes (including seeds with $Q<1$ and $Q>1$), and all 56 horizontal plus 70 lifted octahedron minors. Seven deliberately corrupted inputs are rejected. Ordinary and optimized-mode reports are byte-identical. All inequalities use integers and Fraction; there are no float comparisons or unverified solver answers.

An important regression has its *entire* positive Jensen defect on singular horizontal tuples. Omitting these tuples would invalidate the general equality proof and is explicitly caught by a corrupted-certificate test. Another regression is an even law with an interior atom that violates the claimed symmetric bound when the boundary hypothesis is removed.

The counts describe fixed finite tests, not exhaustive verification of all probability laws or convex bodies. Hashes are integrity records, not independent mathematical validation.

## Open obligations outside the claims

No explicit affine stability modulus or exponent, complete symmetric upper-bound equality class in dimensions at least three, or sharp recursive spectral upper envelope has been proved. The numerical asymptotic constant in v2 is not improved. Bibliographic equivalence with all random-simplex and cone literature has not been excluded. These are scope limitations, not omitted steps in the stated theorems.
