# Independent literal truncation-sharpness semantic review

Reviewed exact input: `entry005-actual-truncation-sharpness-20261007.zip`, Library `[private artifact identity omitted; see archive SHA-256]`, version 0, 835939 bytes, 290 files, SHA-256 `85f444c30899ea9a5b76b7cb912ca10165f5c2302714d5ee199e033a69fd8074`.

## Scope and conclusion

The source establishes the actual literal existential `Entry005.truncationSharpnessGoal`. It does not establish `sharpMainGoal`, the upper bound for every prescribed maximum simplex. No counterexample, quantifier weakening, alternate centroid, fabricated defect, or unproved geometric equality was found in the inspected proof chain. The semantic conclusion is paired with separate compile/ownership/kernel results; this prose is not itself a kernel certificate.

`Targets.lean` was fetched independently from mxym/math at `3c6f6a1a53b0d524af50bd940c3f73f400b41516`; all 4644 bytes were compared, not just theorem names. Its SHA-256 is `8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`. The target definitions retain actual Euclidean volumes, projection onto orthogonal subspaces, intersection-defined projection bodies, a convex-hull pyramid, and the stated dimension-dependent normalization. The stale introductory comment saying no final target inhabitant is claimed is inherited unchanged with the public target file; the new proof lives in its own module.

## 1. Target quantifiers and final closure

`TruncationSharpness.lean:12` has precisely `theorem truncationSharpness : truncationSharpnessGoal`; it takes no extra hypothesis. It supplies `truncation_entryDefect_exact` to the deliberately conditional `truncation_sharpness_from_actual_defect_formula` (`TruncationSharpnessAssembly.lean:14`). Thus the formula is discharged, not silently assumed. Dimensions satisfy d >= 3, alpha > 1/(d-1), C >= 0 and epsilon > 0; the conclusion includes a common t with 0 < t < min(epsilon,1), the exact truncation carrier, nonempty interior, a maximum-inscribed affine simplex, positive defect less than epsilon, and the strict comparison C e^alpha < excess.

The sharpness target existentially chooses S. This is the appropriate obstruction to any improved-exponent inequality asserted for every maximum simplex. It does not show that every maximizing simplex has the displayed excess, and does not prove a best-maximum obstruction. The separate upper-bound target universally quantifies S and is not replaced or solved here. The assembly does not use C >= 0 because its scalar obstruction is valid for all real C; this strengthens a helper and does not weaken the target.

## 2. Actual truncation geometry

`TruncationDefinitions.lean` defines the genuine points e_i and t e_i. `TruncationGeometry.lean:55` proves that the unchanged inequality carrier `{x_i >= 0, t <= sum x_i <= 1}` equals the convex hull of those 2d points. Its proof supplies actual nonnegative convex coefficients summing to one and reconstructs each point. Compactness then follows from the finite convex hull, convexity is direct, and `truncationBody` (`:109`) has that exact carrier by definition. `truncationSet_interior_nonempty` (`:121`) constructs an open strict-inequality neighborhood around the point with all coordinates `(1+t)/(2d)`.

`TruncationVolume.lean:62` proves actual volume `(1-t^d)/d!` by the ambient simplex/removed simplex union and a measure-zero hyperplane overlap. It separately verifies finiteness before passing through ENNReal.toReal; no infinity-to-zero artifact is used. The ambient simplex volume comes from eight selected OpenAI/math proof bodies copied as an exact 6404-byte prefix. An independent GitHub fetch at `adc7f1241b42e322a6451854ab7e4b4c146bf78a` matches both the embedded complete upstream source and the reused prefix; no claim is made to audit the whole upstream repository.

## 3. Intrinsic facets, brightness and actual defect

`TruncationFacetGeometry.lean` gives real unit normals: -e_i, the unit all-ones diagonal, and its negative, with supports 0, 1/sqrt(d), -t/sqrt(d). The literal halfspace representation, top and bottom facet carriers are proved from the inequalities. The top area is obtained using the actual radial cone and its actual ambient-simplex volume, not an assumed area formula. The bottom facet is proved a homothety and its intrinsic area scales in dimension d-1. `TruncationCoordinateFacets.lean` constructs a genuine linear isometry by inserting a zero coordinate and deleting it in the inverse, so each coordinate facet is the actual (d-1)-dimensional truncation with intrinsic Euclidean measure.

Writing c=1/(d-1)!, q=t^(d-1), r=1-q, the resulting actual area-normal vectors and area-support products are (-cr e_i,0), (c 1,c), (-cq 1,-ct^d). `TruncationFacetVectors.lean` proves their equality to the actual chart-derived data. The bottom support is negative and is never used as a probability weight.

`TruncationCenteredHalfspaces.lean` translates by the exhibited interior point and proves every new support strictly positive, exact translated carrier, volume preservation, facet-area preservation and the original entryA/entryDefect by the proved affine invariance. `TruncationActualDefect.lean:19,38` proves the lifted translation is a determinant-one row shear. This legitimately consumes the inherited finite cone-law/pyramid bridge and returns to the original uncentered body.

`TruncationProjection.lean:11` identifies the actual intersection-defined projection body with the genuine facet zonotope. `:29` proves brightness for every unit direction u: c/2 times `r sum |u_i| + (1+q)|sum u_i|`.

The horizontal/lifted sums in `TruncationFacetDeterminants.lean:326,374` range over all ordered tuples, including repetitions. The proof removes zero non-injective terms, partitions injections by use of the two special facets, proves the parallel horizontal minors vanish, computes the paired lifted minors, and obtains d! and (d+1)! multiplicities. After actual facet substitution and positive-factor cancellation, `TruncationActualDefect.lean:249` proves the unchanged actual `entryDefect` is

`t^(d-1) [d(d-1) - (d+1)(d-2)t - 2t^d] / [(d+1)(1-t^d)(d+1+(d-1)t^(d-1))]`.

This theorem assumes only d >= 2 and 0 < t < 1. It has no facet-area, projection, volume, determinant-sum or pyramid identity premise. The scalar-cancellation helper is downstream of real geometry, rather than a replacement invariant.

## 4. Genuine global maximality

`TruncationMaximum.lean:13` proves affine independence of the chosen ordered points `(t e_i,e_1,...,e_d)` for t != 1. Their augmented determinant is 1-t (`:59`) and their convex hull is actually contained in K_t (`:48`).

For arbitrary actual vertex tuples, the pigeonhole principle gives a repeated coordinate ray. Equal vertices give determinant zero. A top/bottom pair on one ray permits a determinant-preserving column operation extracting 1-t; the remaining horizontal minor is bounded by the product of its column l1 norms, each at most 1. This includes arbitrary tuples and degeneracies, and is valid for 0 <= t <= 1.

Crucially, `TruncationConvexDeterminant.lean` proves separate convexity of the augmented absolute-determinant sublevel set and inducts over the slots to extend the vertex-tuple bound to arbitrary points in the convex hull. `truncation_tuple_determinant_bound` (`TruncationMaximum.lean:198`) therefore covers any d+1 inscribed points, not only extreme points. `truncationSimplex_maximumInscribed` (`:208`) takes any genuine affine simplex T contained in the body, applies that bound to T.points, and uses the actual simplex-volume interface with a positive-volume ambient simplex. ENNReal finiteness is proved before converting the comparison back. The resulting maximum relation has exactly the target's universal competitor quantifier.

The implementation uses a column-l1 argument and coordinatewise convexity, rather than relying on the prose's more detailed classification of all vertex patterns or all maxima. The actual theorem needed is nevertheless fully proved. `TruncationSimplexActualVolume.lean` also supplies the absolute real volume (1-t)/d!.

## 5. Same original centroid and literal sInf

`TruncationCentroid.lean:30` obtains each barycentric coordinate of this simplex's own `S.centroid` as 1/(d+1). `:40` proves actual membership in the image-defined `centeredDilation S epsilon` is equivalent to every coordinate being at least -epsilon/(d+1), for epsilon >= 0. The backward implication explicitly inverts the positive homothety factor 1+epsilon.

The coordinates of the chosen simplex are derived from reconstruction and sum-to-one, not stipulated: beta_0=(1-sum x_i)/(1-t), and beta_j=x_j-t 1_{j=i} beta_0. On K_t they are bounded below by -t; the distinct-ray point t e_j attains -t in coordinate i. A different ray exists for d >= 2. Hence containment iff (d+1)t <= epsilon (`:162`). Finally `:201` proves the admissible epsilon set has actual least element (d+1)t and invokes `IsLeast.csInf_eq`, so the target's actual infimum is exactly (d+1)t. It does not exploit an empty or unbounded infimum set and does not substitute the ambient simplex's centroid or an optimized center.

## 6. Positivity, asymptotics and exponent

`TruncationRationalDefect.lean` factors e into t^(d-1) times its coefficient. Its bracket identity is `(d+1)(d-2)(1-t)+2(1-t^d)`, positive in the required domain. It proves a two-sided continuous coefficient limit d(d-1)/(d+1)^2 and then the right-sided actual quotient limit after the geometric equality is supplied.

`TruncationPower.lean:15` proves alpha > 0 and (d-1)alpha-1 > 0. The quotient C e(t)^alpha/((d+1)t) is rewritten as a convergent coefficient times t raised to that strictly positive exponent, and tends to zero. The right-neighborhood filter is nontrivial, so simultaneously eventual strict parameter/defect/comparison conditions produce a genuine t. There is no numerical or asymptotic oracle and no change of exponent. `TruncationSharpness.lean:16,22` expose positivity and the asymptotic for the actual geometric defect itself.

## 7. Deliberate non-claims

No proof here of the prescribed upper-bound Main, explicit optimal upper constants, classification of all maximizing S_p, arbitrary-p excess, infimum over all maximizing simplices, Banach–Mazur estimates, or Rogers–Shephard obstruction. Additional analytic discussion in SHARPNESS_PROOF.md is not included in the kernel-certified claim. No source or frozen bundle was changed, and no publication or external write was performed.
