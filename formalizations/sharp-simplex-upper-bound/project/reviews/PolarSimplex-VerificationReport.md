# Actual polar enclosing simplex: verification and interface

Frozen source: `Entry005/PolarSimplexConstruction.lean`.
SHA256: `25c218de019a59683a5ff589c4c398e91fec9f79b3c511cc4424c02b2d992e67`.
Source size: 22006 bytes. Public inventory: 23 proved theorems and 10 definitions, 33 declarations total.

This module closes the requested actual polar simplex construction. It introduces no axiom, placeholder theorem, facet-area identity, abstract polar-body equality assumption or extra law/witness choice. It neither states nor proves sharp Main. All geometry is derived from the supplied same witness points.

## Construction and proof

For the given affine-independent `w : Fin (d+1) → Space d`, the actual dimension identity gives its full affine basis. Its barycentric coordinates at zero are `λ_i`. The supplied positive-radius ball inside `convexHull(range w)` makes zero an interior point of that hull. The pinned `AffineBasis.interior_convexHull` theorem therefore gives `λ_i > 0`; the standard coordinate sum gives `Σ λ_i=1`.

The finite-dimensional Riesz isometry represents the linear part of each barycentric coordinate by an actual vector `g_i`. Define explicit vertices `v_i = -λ_i⁻¹ • g_i`. Their proved pairings are

```
inner ℝ (w i) (v j) = 1 - (if i=j then 1 else 0)/λ_j.
```

These pairings prove affine independence of the vertices directly: a zero vector combination with zero coefficient sum, paired with `w_i`, forces the coefficient at i to vanish. Thus the constructed `polarWitnessSimplex` is a genuine `Affine.Simplex ℝ (Space d) d` with exactly these vertices. No existence of a simplex with desired halfspaces is assumed.

The actual affine maps `x ↦ λ_i*(1-inner ℝ (w_i) x)` have Kronecker values at the new vertices. Agreement on the full affine basis identifies them with that simplex's barycentric coordinates. The pinned `AffineBasis.convexHull_eq_nonneg_coord` theorem and λ_i positivity give the exact equality

```
simplexSet (polarWitnessSimplex w ha hb hround)
  = {x | ∀ i, inner ℝ (w i) x ≤ 1}.
```

The hull of the finite vertices is compact. If each supplied w_i has norm at most one, Cauchy–Schwarz places the actual closed unit ball in this halfspace set. Conversely the inequality `inner z x ≤ 1` extends from the w_i to their convex hull. Testing at `(b/‖x‖) • x`, a point of the supplied b-ball, gives `b*‖x‖≤1` and the literal outer bound `‖x‖≤b⁻¹` (zero is handled separately).

If each same w_i has actual K support height one, the attained/bounded actual support theorem gives K inclusion. For d≥1 the index family has at least two points. Pairing with a different vertex realizes support exactly one at every w_i. Positivity of every λ and their sum also imply λ_i<1 and w_i≠0.

The exact normalized normals and heights are definitions

```
n_i = ‖w_i‖⁻¹ • w_i,
h_i = ‖w_i‖⁻¹.
```

They have unit norm and positive heights. Normal injectivity is proved geometrically: at v_i the self-normal inner product is negative (λ_i<1), whereas every different normalized normal has positive inner product. Equality of two normalized normals would contradict those signs. Dividing the normalized inequalities by the positive inverse norm proves the actual finite halfspace equality. Dividing their actual raw coordinates by h_i proves `finiteConePoint n h i = raw w_i` exactly. The support of each n_i is also proved to be exactly h_i. There are no facet formulas in this argument.

## Exact original-radius terminal API

`actual_polar_enclosing_simplex_original_radius` requires only the following displayed geometry:

- d≥2 and an actual `ConvexBody (Space d)` K;
- the supplied same raw points `w : Fin(d+1) → Fin d → ℝ`;
- affine independence and norm≤1 for their literal `WithLp.toLp 2` images;
- the actual `b d`-ball contained in their actual convex hull;
- each supplied raw point in `actualPolarBoundaryRaw (K : Set (Space d))`.

It returns P as an actual Affine.Simplex, unit normals n and positive heights, with exactly these ten conjuncts in this order:

1. `simplexSet P = {x | ∀ i, inner ℝ (WithLp.toLp 2 (w i)) x ≤ 1}`;
2. `K ⊆ simplexSet P`;
3. `closedBall 0 1 ⊆ simplexSet P`;
4. `simplexSet P ⊆ closedBall 0 (M d)`;
5. `∀ i, ‖n i‖ = 1`;
6. `∀ i, 0 < heights i`;
7. `Function.Injective n`;
8. `simplexSet P = finiteHalfspaceSet n heights`;
9. `∀ i, finiteConePoint (fun i j => n i j) heights i = w i`;
10. `∀ i, compactSupportHeight (simplexSet P) (WithLp.toLp 2 (w i)) = 1`.

The original radius is exactly `M d = 1 / b d`, not a replacement constant. Polar-boundary membership is the literal support-height-one definition for this same K. No probability law, center, brightness, entryA, entryDefect, pyramid, B identity or finite Minkowski premise appears in this terminal theorem. It works for any supplied witnesses satisfying the stated inputs, so downstream assembly retains its chosen μ, φ, w and r without choosing another law or anchors.

The generic `actual_polar_enclosing_simplex` works already for d≥1, arbitrary positive b and compact nonempty K. `polarWitnessConvexBody` additionally exposes the same constructed simplex as an actual convex body, with exact carrier equality proved by rfl. These definitions are optional convenience interfaces, not assumptions of the terminal result.

## Kernel verification and reproduction

Run `python3 ${HISTORICAL_LOCAL_PATH}`. The script checks the frozen source hash, uses pinned Lean 4.34.1, and runs all three jobs with `-DautoImplicit=false -DwarningAsError=true`. The source compiles into this lane's regular owned `lib/Entry005/PolarSimplexConstruction.olean`. Its compile log is empty and all jobs exit zero.

`Audit.lean/log` contain full signatures for all 33 exports and their axiom inventories; every inventory is contained in `{propext, Classical.choice, Quot.sound}`. `LiteralTerminal.lean/log` restates the full original-radius terminal result and expands the actual finite halfspaces and coordinate atoms to their literal set/function formulas. It also states the K polar-boundary hypothesis as literal support height one. That exact theorem compiled, with only the standard three axioms.

The owned cache links existing dependency oleans read-only from `${HISTORICAL_LOCAL_PATH}`, plus the supplied nine pinned dependency package paths/core in LeanPath.txt. No cache, incoming source, earlier checkpoint, or shared source was modified. The baseline supplied all needed imports; no additional Mathlib build or download was necessary.

Relevant pinned proof provenance: `AffineBasis.interior_convexHull` in `Mathlib/Analysis/Normed/Affine/AddTorsorBases.lean` derives strict barycentric positivity using the exact convex-hull coordinate halfspaces and open barycentric maps. `AffineBasis.convexHull_eq_nonneg_coord` in `Mathlib/Analysis/Convex/Combination.lean` proves that halfspace representation through affine combinations. Both source proofs were read. `InnerProductSpace.toDual` is the pinned finite-dimensional Hilbert Riesz isometry, not an assumed witness matrix inverse or polar theorem.

## Remaining scope

No geometric construction blocker remains in this module. The same-w actual polar simplex, all requested balls/body inclusions, exact finite presentation, injective unit normals, positive heights, actual facet atom identification and support-one values are proved. The upstream supplied hull roundness and boundary inputs must still be instantiated from the same law/assignment in the parent assembly; this theorem does not choose or establish those analytic witnesses. Final sharp Main must be checked in the parent's complete assembled environment. This source alone makes no claim about that final kernel integration or other lanes' proofs.
