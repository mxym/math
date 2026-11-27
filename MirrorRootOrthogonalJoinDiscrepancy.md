# Orthogonal joins preserve hemisphere-extremal spherical cap discrepancy

Let two antipodal samples lie on unit spheres in orthogonal subspaces. Their union is viewed on the unit sphere of the **whole** direct sum: uniform cap area changes with dimension. Nevertheless there is a simple sharp composition law.

**Theorem.** Suppose each sample Xᵢ has Nᵢ points, minimum open hemisphere count Mᵢ, and spherical cap discrepancy 1/2−Mᵢ/Nᵢ (i.e. a hemisphere already attains its supremum over *all* caps). Then their orthogonal union has discrepancy
```
1/2 − minᵢ Mᵢ / (Σᵢ Nᵢ).
```
This holds for any finite number of factors. If the union spans its ambient space of dimension at least three and there are at least two nonempty factors, **only hemispheres maximize**, even if some factors also had nonhemispherical maximizers. Their normals lie entirely in one factor of smallest Mᵢ and minimize its open hemisphere count. This is not a statement about Cartesian products or about a weighted root-length measure.

In particular the [irreducible mirror classification](MirrorRootSphericalCapDiscrepancy.md) now gives the discrepancy and all maximizing equators for **every** finite real reflection system in its essential representation, including arbitrary products and repeated factors. An extraneous fixed direction outside the span is different: if present, the whole sample lies on an equator and the discrepancy is 1/2.

| Orthogonal union | N | Minimum open hemisphere | Discrepancy | Unoriented maximizing equators |
|:--|--:|--:|:--|--:|
| E₆ ⊕ E₈ | 312 | 16 | 35/78 | 27 |
| E₈ ⊕ E₈ | 480 | 57 | 61/160 | 240 |
| I₂(5) ⊕ I₂(7) | 24 | 4 | 1/3 | 5 |
| A₁ ⊕ E₈ | 242 | 1 | 60/121 | 1 |
| d copies of A₁, d≥3 | 2d | 1 | (d−1)/(2d) | d |

## A two-factor inequality for arbitrary antipodal measures

Let μᵢ be centrally symmetric probability measures on the two unit spheres, with cap discrepancies Dᵢ. Use their weighted mixture in the orthogonal direct sum with weights α₁,α₂>0 summing to one. Then, without a hemisphere-extremality assumption,
```
D(mixture) ≤ 1/2 − minᵢ αᵢ(1/2−Dᵢ).
```

Here is the geometric fact behind the change of dimension. For a fixed cap center in the direct sum write aᵢ for the lengths of its two orthogonal projections. For a **uniform random point on the whole sphere** write Rᵢ for its projection lengths. The squared lengths sum to one in both cases. Each Rᵢ has a continuous distribution on [0,1], with positive probability in every open subinterval; conditionally on its length its direction is uniform on the factor sphere. This follows by normalizing independent standard Gaussian blocks. Thus for a positive cosine threshold c and ambient cap area F(c),
```
F(c) = E Fᵢ(c/Rᵢ),                 1/2−F(c) = E [1/2−Fᵢ(c/Rᵢ)].
```
Here Fᵢ is *factor* cap area for the same boundary convention, zero beyond threshold one. In the identity one can use any fixed axis inside factor i by ambient rotation invariance; it need not be the original cap center. In contrast, the factor's contribution to the actual mixture cap uses the original projected axis and threshold c/aᵢ; if aᵢ=0 that contribution and Fᵢ(c/aᵢ) are zero.

The events R₁≥a₁ and R₂≥a₂ partition up to null boundaries; so do R₁≤a₁ and R₂≤a₂. Choose i with Pr(Rᵢ≥aᵢ)≥αᵢ. Monotonicity in the radial length gives F(c)≥αᵢFᵢ(c/aᵢ). Independently choose j with Pr(Rⱼ≤aⱼ)≥αⱼ. The second identity gives 1/2−F(c)≥αⱼ(1/2−Fⱼ(c/aⱼ)).

Write kᵢ for the μᵢ-mass of the projected cap and k=Σαᵢkᵢ for the mixture mass. All kᵢ lie in [0,1/2] for c>0 by antipodality. The factor discrepancy bounds imply
```
1/2−k ≥ αᵢ(1/2−kᵢ) ≥ αᵢ(1/2−Dᵢ) − αᵢFᵢ(c/aᵢ);
     k ≥ αⱼkⱼ        ≥ αⱼ(1/2−Dⱼ) − αⱼ(1/2−Fⱼ(c/aⱼ)).
```
These are exactly the required excess and deficit bounds. They also work in dimension-one factors, whose spherical measure has atoms; use consistently either the open or the closed one-point threshold. At c=0 an open hemisphere has measure Σαᵢkᵢ with each nonzero-projection factor contributing at least αᵢ(1/2−Dᵢ); the count is at most 1/2. The closed case is complementary. Negative thresholds follow from complementation too.

## Sharpness and strictness for finite samples

For counting measure put αᵢ=Nᵢ/N. In an open hemisphere each nonzero-projection factor contributes at least Mᵢ points, and a center in just one factor can attain its minimum. Thus the join minimum is M=min Mᵢ and the upper bound is sharp. For spanning samples Mᵢ≥1, so a hemispherical maximizer must use a single minimizing factor. Repeat the binary theorem to get arbitrary finite joins.

For clarity, in a binary join of total dimension ≥3, the radial comparisons above can be made **strict** for 0<c<1. For each of the two event pairs, either one probability is strictly greater than its αᵢ, or both equal their αᵢ. In the strict-probability case the comparison is strict if the factor quantity being multiplied is positive; if it is zero the ambient F(c) and 1/2−F(c) are themselves positive. In the exact-probability case choose a factor of dimension ≥2, which exists, with 0<aᵢ<1. Its cap area Fᵢ(c/r) strictly increases for c<r<1, so integrating over r>max(aᵢ,c) makes the first comparison strict. The factor decrement 1/2−Fᵢ(c/r) is positive for all r>0, so the second comparison is strict from the omitted region r>aᵢ. This proves strictness for both deviations, with no generic-position assumption.

At c=1 there is at most one point, whereas the spanning finite antipodal union has N≥2d≥6 and M≤min Nᵢ/2≤N/4, so 1/N<1/4≤1/2−M/N. This proves the maximizing-cap characterization. The total-dimension-two exception is genuine: A₁⊕A₁ is a square on the circle and a closed arc between neighboring vertices also maximizes.

## All-aperture composition, not just discrepancy

For finite antipodal unit samples define Aₖ as the infimum squared norm of a vector forcing at least k scalar products ≥1, and Bₖ as the supremum squared norm permitting at most k scalar products >1. Use 0≤k≤N/2; A₀=0 and Bₖ may be infinite. Then the entire positive-threshold pair of envelopes composes by
```
A(join,k) = min_{i+j=k} [A(left,i)+A(right,j)],
B(join,k) = max_{i+j=k} [B(left,i)+B(right,j)].
```
The squared norm adds across orthogonal blocks, and their scalar-product constraints are independent. In the lower problem distribute k required hits among the blocks; in the upper problem distribute k allowed hits (unused budget can be allocated up to the half-sample capacities). Combining optimal block witnesses, or arbitrarily long witnesses on an unbounded block, attains the corresponding endpoint. Use the same root-length convention for both blocks. For example two orthogonal unit hexagons have A=(0,1,4/3,7/3,8/3,16/3,8) and B=(8/3,16/3,∞,∞,∞,∞,∞).

[Calculator and exact rational convolution](mirror-join-discrepancy.js):
```sh
node mirror-join-discrepancy.js E6 E8
node mirror-join-discrepancy.js I2:5 I2:7
```
The argument for composition is analytic; the code checks the tabulated examples and independently known cross-polytope spectra, not a numerical discretization of cap centers. For background on the discrepancy definition and general enumeration see [Heitsch–Henrion](https://www.wias-berlin.de/people/henrion/spher-cap-disc-online.pdf).
