# Scope and adversarial review

**Draft, 2026-11-18.** This is a continuation of the repository's fixed-mass first-moment work, not another independent refutation. No worldwide priority, independent human refereeing, journal submission, release or formal verification is claimed. The mathematical claim is the one in [the proof](README.md); this file is a verification guide.

## Primary-source comparison

1. [Heilman, *Stable Gaussian minimal bubbles*, Problem 1.15 and Conjecture 1.16](https://doi.org/10.1007/s00526-026-03408-z) gives the prescribed-volume question for more than three cells in dimension at least the number of cells minus one. Its centering by a fixed common vector divided by the respective masses adds a constant when the masses are held fixed. The three-cell conclusion in our note concerns the same first-moment functional, not the printed range of that conjecture.
2. [Zhang, preceding one-parameter counterexample, canonical proof](../gaussian-fixed-mass-propeller-counterexample/paper.md) already gives exact-mass strict improvement for every four-cell mass vector of the form $(p,(1-p)/3,(1-p)/3,(1-p)/3)$ with $0<p<1/4$. Its equal-mass ball exchange, and the use of a nonzero tangential difference of first moments, are prior work. The present step is the order comparison valid for every triple of indices and arbitrary offsets. This removes the earlier mass-family and cell-count restrictions. [Archived revision](https://doi.org/10.5281/zenodo.23272917).
3. [Heilman, Mossel and Neeman, Theorem 2.6](https://arxiv.org/html/1403.0885v3) already treats every nonuniform mass vector for a *different functional*, the positive- or negative-correlation Gaussian agreement probability. Its Sections 3–5 use a volume-preserving normal variation and a nonconstant interface score for the nonlocal noise operator. At correlation zero the probability is fixed by the masses. Our $F$ is the coefficient of degree one in the Hermite expansion, i.e. the derivative at zero, not the value at a fixed nonzero correlation. A strict positive difference for every positive argument is compatible with zero derivative at zero (e.g. a quadratic difference); the competitor could also depend on the argument.
4. [Heilman, *Euclidean Partitions Optimizing Noise Stability*](https://arxiv.org/html/1211.7138v2), notably Section 2 and the questions in Section 8, distinguishes zero-correlation first moments, equal-volume results and optimization at positive correlation. [Heilman, *On the Propeller Conjecture*](https://arxiv.org/html/2610.32158v1), Theorem 1.1, treats an upper bound with *unrestricted* cell masses. Strictness below that upper bound at a particular partition does not provide an improving partition **at the same masses**.
5. [Zhang, prescribed-mass centroid ellipsoid, Section 5](../gaussian-prescribed-mass-centroid-ellipsoid/paper.md) treats every positive mass vector, but its sharp quadratic form uses a **mass-dependent label-space metric**. The paper explicitly distinguishes that quantity from the ordinary sum of squares used here. [The equal-mass companion](../gaussian-balanced-simplex-all-k/README.md) concerns the uniform vector excluded from the present theorem. [Milman–Neeman](https://arxiv.org/abs/1805.10961) minimize unpenalized Gaussian perimeter, not this moment functional.

The literature screen queried combinations of “Gaussian first moments”, “prescribed masses/volumes”, “translated regular simplex”, “first Hermite”, “Propeller”, and “Heilman Conjecture 1.16” in web and scholarly indexes, plus the repository’s fixed-mass, balanced and label-metric work. No checked source above states strict local nonoptimality of the unweighted first-moment score for **every** nonuniform positive vector. This is a bounded search, not a proof of first discovery. Separate publication or retrospective coverage may exist.

## Attempts to break the argument

- **Normalization:** the proof uses unnormalized moments, not conditional means (which would divide by $p_i$). Independent Gaussian coordinates are only an auxiliary representation. The common score direction is independent of the winning label, so auxiliary moments equal the moments in the true $(k-1)$-dimensional Gaussian space. A component in an extra orthogonal dimension cannot account for the exchange gain.
- **Tangent or normal?** A nonzero coordinate in the auxiliary space is not by itself a tangent vector. For a *third* index $\ell$ the projection $Pe_\ell$ belongs to the actual simplex span, is nonzero, and is orthogonal to $e_i-e_j$. Since $D=z_i-z_j$ belongs to this span, $D\cdot Pe_\ell=D_\ell$. No all-pairs regularity assumption is made.
- **Equal offsets among some cells:** only one strictly ordered pair of offsets is needed. For a repeated offset the comparison becomes equality, as expected. At the uniform vector the argument supplies no contradiction. For two labels there is no third coordinate, and the theorem does not apply.
- **Faces with very small or very unequal probabilities:** the relative interior of the $i,j$ face always exists, regardless of the offsets. Choose the two adjusted scores tied strictly above every other score in the auxiliary space, then project. Moving a small distance in the tangent direction preserves the strict inequalities. The proof requires no lower bound uniform up to the boundary of the mass simplex.
- **Sign and exact mass:** the lower-scoring ball must be taken from $C_i$ and the higher-scoring one from $C_j$ for $D=z_i-z_j$. The new moments are $z_i+v,z_j-v$. Ordering the scalar score on the two whole balls and matching their Gaussian masses (not their Euclidean radii) makes $D\cdot v>0$. The exact quadratic remainder has positive sign.
- **Locality:** only a set of mass $2\delta$ changes; equivalently the sum of the cells' symmetric-difference masses is $4\delta$. “Local” refers to this measure distance, not a claim about all notions of smooth topology.
- **Existence:** first demonstrate that offsets realizing any positive mass vector exist; separately, obtain an unrestricted maximizer by weak-star compact relaxation and purification on a fiber with *all* moments fixed. The proof needs neither uniqueness of the offsets nor the shape of the unrestricted maximizer.
- **What is not proved:** neither the identity of the maximizing partition nor its exact score. No assertion about the equal-mass finite-correlation Standard Simplex Conjecture is made.

## Independent elementary check in three cells

For distinct $i,j,\ell$ and $k=3$, completing the square in the product of the two densities yields
$$
 I_{i\ell}=\frac{e^{-(b_i-b_\ell)^2/4}}{2\sqrt\pi}
    \Phi\!\left(\frac{b_i+b_\ell-2b_j}{\sqrt6}\right).
$$
Indeed after completing the square the remaining integral is the expectation of $\Phi(T-b_j)$ for $T\sim N((b_i+b_\ell)/2,1/2)$. Subtract an independent standard normal to obtain the displayed probability. The optional standard-library diagnostic compares this independent expression to the defining integral, checks fixed, asymmetric four- and five-cell examples, repeats a common-offset and permutation test, and checks the equal-offset negative control:

```sh
python3 checks.py
```

The numerical test is illustrative only. The proof for arbitrary real offsets, all cell counts and actual mass-preserving exchanges is analytic.
