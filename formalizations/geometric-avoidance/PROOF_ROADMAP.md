# Affine geometric avoidance proof roadmap

## Result and scope

The Lean theorem `ContinuumGeometric.geometric_main_target` proves the following statement.

For every real number ε with 0 < ε < 1, there is a set E ⊆ ℝ such that:

1. E is compact and E ⊆ [0,1].
2. Its Lebesgue measure satisfies λ(E) > 1 − ε.
3. For every a,b,q ∈ ℝ with a ≠ 0 and 0 < q < 1, and for every N ∈ ℕ, there is an n ∈ ℕ with n ≥ N and a qⁿ + b ∉ E.

Thus a **single E**, chosen after ε and before a, b, q, and N, works for every one of these progressions simultaneously. Each progression has arbitrarily late terms outside E. The conclusion is not that every term is outside E, or that an entire tail is outside E.

In Lean, the unchanged proposition definitions in `ContinuumGeometric/Target.lean` are:

```lean
def AvoidsGeometricTails (E : Set ℝ) : Prop :=
  ∀ (a b q : ℝ), a ≠ 0 → 0 < q → q < 1 →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a * q ^ n + b ∉ E

def MainTarget : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc 0 1 ∧
      ENNReal.ofReal (1 - ε) < volume E ∧ AvoidsGeometricTails E
```

`volume` here is the standard Lebesgue measure on the ordinary real numbers, using Mathlib's `Real.measureSpace`. Its values lie in the extended nonnegative reals `ℝ≥0∞`; `ENNReal.ofReal` embeds the positive real number 1 − ε into that type. This is an actual measure inequality, not a density surrogate, a finite counting measure, or a `toReal` conversion. Compactness supplies measurability, and containment in [0,1] supplies finiteness.

The final declaration in `ContinuumGeometric/MainProof.lean` is a closed theorem of type `MainTarget`. In particular, it has no blocker-existence or probability hypothesis. This roadmap explains that completed original theorem. A stronger continuum leading-exponent theorem with a nonlinear remainder is a separate **written-only** result and is outside this Lean theorem's scope. The construction here uses exact geometric points throughout. The existence proof is noncomputable and does not provide a practical numerical description of E.

Source filenames below are relative to the Lean project root. Unless a nested namespace is displayed, theorem names have the prefix `ContinuumGeometric.`. The companion [theorem map](THEOREM_MAP.md) gives the module-level reading order.

## Why the excluded boundary cases matter

The strict hypotheses on a and q are necessary for this all-center conclusion with a nonempty E. If y ∈ E:

- Allowing a = 0 makes the sequence constant at y by taking b = y, even with q = 1/2.
- Allowing q = 0 makes every term with n ≥ 1 equal to b. Taking a = 1, b = y, and N = 1 defeats the conclusion. This argument does not rely on a convention about 0⁰.
- Allowing q = 1 makes the sequence constant at a + b. Take a = 1 and b = y − 1.

The required positive measure guarantees that E is nonempty. The theorem also cannot have the same strict inequality at ε = 0, because E ⊆ [0,1] implies λ(E) ≤ 1. Other ratio ranges are not part of the stated target.

## The construction in one view

Instead of constructing E directly, construct an open, one-periodic set U ⊆ ℝ with

λ(U ∩ [0,1)) < ε

that hits every requested progression tail. Then set E = [0,1] ∖ U. The work is to make U small while preserving **every** real center and parameter.

The proof first constructs a small periodic blocker for a fixed compact range of positive exponents, a fixed integer coefficient scale, and a fixed original tail. This local construction uses finite random routing tables. A finite family of parameter signatures controls the continuum of parameters, and an open repair set handles the centers missed by the chosen finite outcome. Finally, countably many such blockers and their reflections cover every coefficient, ratio, and tail.

For a one-periodic set S, write

D(S) = λ(S ∩ [0,1)).

This is exactly `unitDensity`, defined in `ContinuumGeometric/RoutingInterfaces.lean`; one-periodicity means x + 1 ∈ S if and only if x ∈ S. All density bounds below therefore concern genuine Lebesgue measure on a fundamental interval.

## The compact blocker statement

Fix K ∈ ℕ with K ≥ 2, k ∈ ℤ, N ∈ ℕ, and 0 < δ < 1. Define

ΘK = [1/K,K] × [1,2],

and, for θ = (s,t) ∈ ΘK, define the exact points

Fₙ(x,θ) = x + t 2ᵏ ((1/2)ⁿ)ˢ = x + t 2ᵏ⁻ˢⁿ.

`PowerParams`, `powerPoint`, and `dyadic` formalize this notation. The intermediate proposition `SmallCompactBlockerSpec` asks for an open, one-periodic H with D(H) < δ such that

for every x ∈ ℝ and every θ ∈ ΘK, there is n ≥ N with Fₙ(x,θ) ∈ H.

The compact rectangle includes its endpoints. The center x ranges over all reals. No rational approximation is made. The theorem `smallCompactBlockerSpec_proved` in `ContinuumGeometric/MainProof.lean` constructs H and proves this specification.

We now describe that construction for a fixed K, k, N, and δ, taking the terminal success probability p = δ/12. Hence 0 < p < 1.

## Strict activation and actual original indices

A logarithmic output window with start u and length ℓ activates the original index j precisely when

u < s j − k < u + ℓ.

Both endpoints are excluded. An active point has displacement

2⁻⁽ᵘ⁺ℓ⁾ < Fⱼ(x,θ) − x < 2¹⁻ᵘ.

The lower bound uses t ≥ 1 and the strict upper activation inequality; the upper bound uses t ≤ 2 and the strict lower inequality. Neither bound restricts x.

Choose the stride

m = ⌈3/(1/K)⌉ + 2,    η = 1/(2mK).

Then m > 0 and m/K > 3. Candidate indices are original natural numbers j = m r, where r is only an enumeration label. The requested tail condition remains **N ≤ m r**, never merely N ≤ r.

If all windows lie before U + T, every active label satisfies

r < B(U,T,k),    B(U,T,k) = ⌈(U + T + |k|)/3⌉ + 1.

Thus the finite global test set consists of the multiples m r with r < B(U,T,k) and N ≤ m r. The absolute position U, the signed scale through |k|, and the additive constant are retained in this bound.

The elementary count behind activation is the number of integers in an open interval:

# {r ∈ ℤ : α < h r < α + ℓ}
= ⌈(α + ℓ)/h⌉ − ⌊α/h⌋ − 1
≥ ℓ/h − 1.

With h = m s ≤ mK and ℓ ≥ 2mK, this is at least ηℓ. The start guard K N ≤ u + k makes all active original indices lie in the requested tail. The actual construction imposes

U ≥ ⌈K N + |k|⌉ + 5,

which also gives U ≥ 4 and the required signed-shift guard.

At a vertex with M − 1 selector children of common length ℓ, there are at least η(M − 1)ℓ active edge/index pairs for every θ. Its candidate family contains exactly the finite edge/index pairs that can become active somewhere in the full rectangle ΘK, so it has size

P ≤ (M − 1) B(U,T,k).

Filtering that family at θ recovers exactly the active arithmetic tests. Completeness and injectivity of its enumeration are proved rather than assumed.

Sources: `ContinuumGeometric/Activation.lean` (`activation_card_exact`, `activation_card_uniform`); `ContinuumGeometric/ShiftedActivation.lean` (`compact_shifted_original_activation`); `ContinuumGeometric/CandidateBounds.lean` (`activeOriginalIndices_count_bounds`, `mem_potentialOriginalPairs_exact`, `candidatePairEnumeration_complete`, `candidatePairEnumeration_injective`, `activeOriginalPairs_eq_potential_filter`); `ContinuumGeometric/RoutingLocalProbability.lean` (`scheduled_vertex_active_count`).

## A finite tree with actual periodic tables

Use a complete ordered M-ary tree of depth d. All M children at every internal vertex have logarithmic windows. The first M − 1 children have selector tables; the last is the default child. Leaves have terminal tables. The default edges and their descendant subtrees are included in every span and ordering estimate.

Given gap g and terminal length L, define the span Tₕ of a height-h tree by

T₀ = 0,
T₁ = M L + (M − 1)g,
Tₕ₊₁ = 2M(g + Tₕ) + (M − 1)g    for h ≥ 1.

At height one, an edge window has length L. At greater height, it has length g + Tₕ for the child-tree span Tₕ. Its window, following gap, and child subtree occupy a block of twice that length. Sibling blocks are separated by gap g. Placement is in preorder starting at U. The total span is exactly

T = A L + B g,

where A and B are natural numbers depending only on M and d.

For an edge with start u and length ℓ, its endpoint is e = u + ℓ − 1. Its selector table has 2ᵉ⁺³ entries. A leaf uses its final incoming edge endpoint in the same way. The table key at grid size G is

keyG(z) = ⌊G z⌋ mod G = ⌊G fract(z)⌋.

This is an exact half-open periodic grid, including negative z and integer wrap. The table tag, identifying the edge or leaf, is part of its address. Finer dyadic keys determine all coarser dyadic keys by integer division.

Sample every selector entry independently with probability 1/2 of being true, and every terminal entry independently with probability p, independently of all selectors. These are finite product weights. At a point z, read the selector entries at the current vertex in child order, take the first true child, or take the default if all are false. Repeat to reach a leaf. Put z into the routed set Bω if that leaf's terminal entry at z is true.

Conditioning on all selectors fixes the selected terminal address at z; its terminal bit has success probability p. Thus Pr(z ∈ Bω) = p for every real z. Later, the proof shows that Bω is an actual finite periodic grid set, giving its measurability and expected density E[D(Bω)] = p.

Sources: `ContinuumGeometric/RoutingTemplate.lean` (`RoutingTemplate.span_affine`, `RoutingTemplate.edge_span_bound`); `ContinuumGeometric/RoutingModel.lean` (`chooseRoutingChild`, `routeLeaf`, `routedSet`); `ContinuumGeometric/RoutingGeometry.lean` (`periodicGridKey_fract`, `periodicGridKey_refinement`); `ContinuumGeometric/FiniteRoutingProbability.lean` (`finiteRoutingWeight_sum`, `actual_routedSet_probability`, `actual_routedSet_expected_density`).

## Stable centers preserve earlier routing decisions

For every edge with start u, set its predecessor endpoint to b₀ = u − g − 1. The origin guard U ≥ g + 1 makes this natural-number subtraction exact. The proved preorder relation says that **every** earlier edge endpoint is at most b₀, not just the previous sibling's endpoint.

Call x stable at this edge if the grid of size 2ᵇ⁰⁺³ has no boundary in

(x, x + R],    R = 2⁻⁽ᵇ⁰⁺ᵍ⁾ = 2¹⁻ᵘ.

A boundary at x itself is allowed, consistently with left-closed, right-open cells. Every active point lies strictly between x and x + R. It therefore has the center's predecessor key and, by refinement, all earlier selector keys. Define the stable-center set by requiring this at every edge, including the first edge's harmless extra condition.

For one grid of size G, the bad centers form the periodic union of intervals [j/G − R,j/G). Its density is at most G R, even when these intervals overlap. In the predecessor grid this product equals 2³⁻ᵍ, independently of b₀. Therefore

D(unstable centers) ≤ (# edges) 2³⁻ᵍ < p,

once g is chosen. This exceptional set is determined by the geometry before sampling any tables.

The route connection is important. A local test first forces entry to a specified nondefault child, then follows the ordinary routing rule below it. At a vertex where the center takes the default, all earlier sibling selectors are false at the center. Stability preserves the necessary ancestor and earlier-sibling reads at the active point. If that point's own selector bit is true, its actual global route therefore enters the specified child, agrees with its local route, and a true local terminal bit implies membership in Bω. This is a proved local-to-global implication, not a replacement definition of success.

Sources: `ContinuumGeometric/RoutingPreorder.lean` (`preorderActualWindows_eq_schedule`, `RoutingTemplate.earlier_edgeEnd_add_gap_le`, `RoutingTemplate.earlier_edgeEnd_le_predecessorBoundary`); `ContinuumGeometric/RoutingStableMeasure.lean` (`unitDensity_gridBoundaryBad_le`); `ContinuumGeometric/RoutingLocalHit.lean` (`actual_local_success_mem_routedSet`); `ContinuumGeometric/RoutingStableGeometry.lean` (`actual_stable_earlier_address_agreement`, `actual_stable_local_success_mem_routedSet`).

## The address separation needed for probability

Fix a center x, parameters θ, and a vertex. Consider its active edge/index pairs. A pair's **own address** is its selected child's selector-table address at the corresponding geometric point. Its local terminal address may depend on every selector bit.

The geometry proves three facts:

1. The own addresses of distinct active pairs are distinct.
2. None is an exposed center address, where the exposure consists of the selector address at x for every selector edge.
3. For every complete selector assignment, the local terminal addresses of distinct active pairs are distinct.

For pairs in different children, the table tags already separate own addresses. Within a child, consecutive stride labels differ by at least three output-log units, making their offsets differ by a factor at least eight. At the own grid scale, every active point is more than four cells from the center and distinct active points are more than 28 cells apart. Since u ≥ 4, every offset is less than 1/8, which prevents modulo-one collisions. Equality of terminal addresses would give the same leaf and hence the same child, and refinement from that leaf's terminal grid to the own grid would contradict own-address separation.

The third fact holds even when own bits are false and local paths share auxiliary selector reads. No blanket independence of adaptive routes is asserted.

Sources: `ContinuumGeometric/RoutingActiveGeometry.lean` (`active_power_gridAddress_ne_center`, `active_subsequence_gridAddress_ne`, `active_original_gridAddress_injective`); `ContinuumGeometric/RoutingTreeBounds.lean` (`localRouteLeaf_grid_bounds`); `ContinuumGeometric/RoutingSeparation.lean` (`actual_local_address_separation`, `active_original_local_address_separation`).

## Exact joint probability on a center atom

A center atom A fixes the selector bits at all exposed center addresses. It fixes the center's entire route. Let J be the number of active pairs for the current parameters. Pair i succeeds when its own selector bit is true and its locally routed terminal bit is true.

The proof obtains the exact joint identity

Pr(A and every pair misses) = Pr(A) (1 − p/2)ᴶ.

Here is the order of averaging that justifies it.

1. Fix **all** selector coordinates, including auxiliary ones. Local terminal addresses are now deterministic and distinct. Averaging the independent terminal bits gives a factor 1 − p for each true own bit and a factor 1 for each false own bit.
2. Multiply the selector product weight by the indicator of A. This factors as the mass of A times point masses at exposed coordinates and independent fair laws at unexposed coordinates.
3. The own coordinates are distinct and unexposed. Each of their factors averages to (1/2)(1 − p) + (1/2) = 1 − p/2. All unused coordinates average to 1.

This computes a joint probability without dividing by Pr(A), so a zero-mass atom would cause no difficulty. The finite formulas also admit p = 0 and p = 1; nonnegativity for probability inequalities uses 0 ≤ p ≤ 1. The actual construction uses 0 < p < 1.

Since J ≥ η(M − 1)ℓ, the miss factor is at most

exp(−pJ/2) ≤ exp(−λℓ),    λ = pη(M − 1)/2.

Sources: `ContinuumGeometric/FiniteRoutingProbability.lean` (`terminal_average_local_miss`, `center_atom_weight_factorization`, `joint_center_atom_all_miss`); `ContinuumGeometric/RoutingLocalProbability.lean` (`actual_fixed_parameter_joint_miss`); `ContinuumGeometric/RoutingEntropy.lean` (`fair_selector_terminal_miss_window_bound`).

## A finite bound for all real parameters

A finite union bound cannot be applied directly to the uncountable parameter rectangle. Instead, at a fixed real center x, encode the complete active local readout using finitely many affine-cut signs in coordinates (s, log t).

Activation is specified by two affine cuts, s j − k − u and u + ℓ + k − s j, both strictly positive. For a relevant lifted grid boundary β = h/G − x > 0, the sign of the displacement minus β is exactly the sign of

s log((1/2)ʲ) + log t + k log 2 − log β.

Only lifted boundaries strictly between x and x + 2¹⁻ᵘ are needed. There are at most G 2¹⁻ᵘ + 1 of them, uniformly in x. The subtree span bound ensures that the local finest endpoint b satisfies b + 1 ≤ u + 2ℓ. With G = 2ᵇ⁺³, each candidate therefore contributes at most 3 + 2²ℓ⁺³ cuts, including the activation cuts.

All three signs, negative, zero, and positive, are retained. In particular, points exactly on an activation boundary are inactive, and points exactly on a cell boundary receive the correct half-open key.

For m affine cuts in the plane, the arrangement theorem bounds realized three-sign patterns by 2m² + 1, and provides representatives in the closed rectangle with the convenient bound 20(m + 5)². A direct reason for the quadratic bound is that adding a nonconstant cut restricts the old cuts to its zero line, where n affine functions have at most 2n + 1 sign patterns; only old patterns meeting that line can split. Constant and identically zero cuts are handled separately. Choosing representatives only for patterns realized in the rectangle also retains rectangle edges and degenerate cases.

Consequently, P candidate pairs admit a representative family of size at most

Q(P,ℓ) = 20 [P(3 + 2²ℓ⁺³) + 5]².

The key factorization theorem proves that a local finest key determines every selector read below that child and the resulting terminal key. The signature stores `none` for an inactive pair and `some(key)` for an active pair. Thus the representatives preserve the **actual all-miss event** for every table outcome:

for every θ, there is a representative θ′ such that, for every complete outcome ω, the all-miss events at θ and θ′ agree.

The representative is chosen before ω. It may depend on x, but the proof only needs a pointwise probability bound at each x; it never needs a measurable selection of representatives as x varies.

Applying the finite union bound on a center atom gives

Pr(A and some θ has all pairs miss) ≤ Pr(A) Q(P,ℓ) exp(−λℓ).

Sources: `ContinuumGeometric/LineSignBound.lean` (`realizedLinePatterns_card_le`); `ContinuumGeometric/SignFiberCount.lean` (`card_le_oldPatterns_add_two_zeroPatterns`); `ContinuumGeometric/Planar.lean` (`realizedPlanePatterns_card_le`, `arrangementRepresentativeBound`); `ContinuumGeometric/GridCutBridge.lean` (`power_grid_cut_sign`, `activation_cut_signs`); `ContinuumGeometric/LocalSignatures.lean` (`actual_local_representatives_entropy_bound`); `ContinuumGeometric/RoutingFactorization.lean` (`actual_routing_local_representatives`); `ContinuumGeometric/RoutingLocalProbability.lean` (`actual_continuum_joint_miss_bound`).

## Choosing parameters without a circular size argument

The finite construction is chosen in the following dependency order:

1. Fix K, k, N, δ, and set p = δ/12.
2. Choose m from K and set η = 1/(2mK).
3. Choose M ≥ 2 large enough that κ = pη(M − 1)/2 − 4 log 2 > 0.
4. Choose d > 0 so that (1 − 2⁻⁽ᴹ⁻¹⁾)ᵈ < p.
5. With the finite edge count now fixed, choose g ≥ 4 so that (# edges) 2³⁻ᵍ < p.
6. Only then choose U and L, with all tail, scale, span, and entropy guards.

For the last step, retain the complete signature cost:

Q(P,ℓ) ≤ 5120(P + 1)² exp(4 log 2 · ℓ).

The +1 matters: at P = 0, Q(0,ℓ) = 500, not zero. Using T ≤ U, |k| ≤ U, P ≤ (M − 1)B(U,T,k), and ℓ ≥ L gives

Q(P,ℓ) exp(−λℓ)
≤ 46080 M²(U + 1)² exp(−κL).

Set C₀ = 46080 M², C = log(C₀/p) + 1, and

L(U) = Lmin + ⌈[4 log(U + 2) + max(C,0)]/κ⌉,

where Lmin = ⌈2mK⌉ + 1. The lower bound on this ceiling proves the **strict** entropy inequality

C₀(U + 1)² exp(−κL(U)) < p.

The upper bound gives L(U) = O(log U). Since the already fixed tree has span A L(U) + B g, that span is at most U for every sufficiently large integer U. Choose such a U also satisfying

U ≥ max(⌈K N + |k|⌉ + 5, g + 1, |k|).

Thus making the window long enough for entropy decay is compatible with fitting the whole tree before 2U. No choice depends on x, θ, any random outcome, or a later parameter. The source proves this late-integer existence, rather than simply saying to choose U and L sufficiently large.

Sources: `ContinuumGeometric/RoutingChoices.lean` (`exists_branching_decay`, `exists_default_depth_budget`, `exists_stable_gap_budget`); `ContinuumGeometric/EntropySchedule.lean` (`scheduledWindow_affine_span_eventually`, `entropy_budget_of_log_lower`, `exists_late_entropy_schedule`); `ContinuumGeometric/RoutingEntropy.lean` (`signature_entropy_exp_bound`, `signature_entropy_position_bound`); `ContinuumGeometric/RoutingSchedule.lean` (`exists_routing_schedule`, `routingSchedule_node_entropy_lt`).

## From center atoms to the global failure bound

For a fixed center, the probability that its actual route never takes a default child is

(1 − 2⁻⁽ᴹ⁻¹⁾)ᵈ < p.

The proof partitions by nondefault leaves and computes the finite product of the required earlier-false and selected-true bits along each prescribed path. It does not assume that adaptively chosen paths are independent.

The center atoms form an exact partition. Within an atom whose center route has a default, choose one default vertex from that fixed route. That **same vertex** serves every selector assignment in the atom. At a stable center, if the global tests fail for some parameters, every active local pair at the chosen vertex must miss: otherwise the local-to-global implication would put a tested point in Bω.

The continuum estimate and the schedule bound this joint failure probability by Pr(A)p on each such atom. Sum over atoms; their masses sum to one. There is no additional factor for the number of vertices, leaves, or atoms. Adding the no-default possibility gives a global missed-center probability at most 2p at every stable real center.

Sources: `ContinuumGeometric/NoDefaultProbability.lean` (`actual_routeHasNoDefault_probability`); `ContinuumGeometric/RoutingCenterAtoms.lean` (`center_atom_default_vertex_exists`, `actual_center_atom_partition`); `ContinuumGeometric/RoutingLocalProbability.lean` (`scheduled_vertex_continuum_joint_miss_bound`); `ContinuumGeometric/RoutingStableProbability.lean` (`actual_missed_center_forces_vertex_miss`, `actual_stable_missed_center_probability_le`).

## Open buffers and a closed missed-center set

The global routed set is exactly a union of canonical periodic half-open grid cells at endpoint U + T − 1. Write its grid size as G = 2ᵁ⁺ᵀ⁺², and set r = p/(8G) > 0. For each outcome form the actual open metric thickenings

B₁,ω = {z : there exists y ∈ Bω with |z − y| < r},
B₂,ω = {z : there exists y ∈ Bω with |z − y| < 2r}.

These are unions of open balls of the indicated radii about points of Bω; they are empty if Bω is empty. Then Bω ⊆ B₁,ω ⊆ B₂,ω. Finite-cell length bounds, with integer periodization to include wrap, prove

D(B₂,ω) ≤ D(Bω) + 4Gr = D(Bω) + p/2 < D(Bω) + p.

Define Rω to be the set of centers x for which **there exists θ ∈ ΘK** such that every finite test activated by any routing window fails to lie in B₁,ω. Failure of one test means either that it is inactive or that its point is outside the open set B₁,ω. Since activation and hitting are open conditions, the failure relation is closed in ℝ × ΘK. Projection along the compact parameter space ΘK is closed. Hence Rω is closed, measurable, and one-periodic.

The probability estimate above applies to this precise Rω because Bω ⊆ B₁,ω. Integrating over the real interval [0,1), and using finite-sum Fubini, gives

E[D(Rω)] ≤ 2p + D(unstable centers) ≤ 3p.

On unstable centers the only bound needed is probability ≤ 1. Also

E[D(B₂,ω)] ≤ E[D(Bω)] + p = 2p.

The normalized finite weights therefore have an outcome ω with

D(B₂,ω) + D(Rω) ≤ 5p.

The finite averaging argument allows zero weights and proves nonemptiness from normalization. It selects one outcome for the integral quantity, not a different outcome at each center.

Sources: `ContinuumGeometric/RoutingGlobalGrid.lean` (`actual_routedSet_finite_grid`); `ContinuumGeometric/PeriodicRepair.lean` (`periodicGridSet_eq_integerPeriodization`, `unitDensity_periodicGridSet_double_buffer_le`, `unitDensity_grid_budget_double_buffer_lt`); `ContinuumGeometric/ClosedProjection.lean` (`isClosed_powerMissedCenters`); `ContinuumGeometric/RoutingMeasure.lean` (`expectedUnitDensity_eq_lintegral_probability`, `exists_outcome_le_expectation`, `exists_powerRouting_outcome_density_add_le_of_stable`).

## Repairing every center with a strictly small open set

For the selected outcome, abbreviate R = Rω and B₂ = B₂,ω. Closedness and periodicity give an open, one-periodic cover V ⊇ R with

D(V) < D(R) + p.

This cover is constructed using shrinking metric thickenings of R. Their measures converge down to D(R) under the finite measure obtained by restricting Lebesgue measure to [0,1). Periodic thickenings automatically retain wrap near both endpoints. The cover is not assumed and is not replaced by all of ℝ.

Set H = B₂ ∪ V. Then

D(H) ≤ D(B₂) + D(V)
< D(B₂) + D(R) + p
≤ 6p = δ/2 < δ.

For any x and θ there are two cases:

- If x ∉ R, one of the finite active original tests has index n ≥ N and hits B₁,ω ⊆ H.
- If x ∈ R, then x ∈ V. Because s ≥ 1/K > 0, the infinite sequence Fₙ(x,θ) converges to x. Openness of V gives a term in V with n ≥ N. This repair index need not belong to the finite test set.

This last case removes every exceptional center, rather than proving an almost-everywhere version of the desired blocker. It completes `SmallCompactBlockerSpec` with a strict density bound.

Sources: `ContinuumGeometric/PeriodicRepair.lean` (`closed_onePeriodic_open_cover`, `periodic_power_outcome_repair`); `ContinuumGeometric/ClosedProjection.lean` (`power_tail_hits_open`, `power_repair_all_centers`); `ContinuumGeometric/RoutingAssembly.lean` (`actual_routing_blocker_of_actual_stable_miss`); `ContinuumGeometric/MainProof.lean` (`smallCompactBlockerSpec_proved`).

## Covering every sign scale ratio and tail

For every real q ∈ (0,1), there is a positive real s with

q = (1/2)ˢ,    qⁿ = ((1/2)ⁿ)ˢ for every n ∈ ℕ.

For example, s = log(q)/log(1/2). Every s > 0 belongs to [1/K,K] for some natural K ≥ 2. For every a ≠ 0 there are a sign σ ∈ {−1,1}, an **integer** k, and t ∈ [1,2) with

a = σ t 2ᵏ.

Negative k are essential to include arbitrarily small coefficients. All these identities hold exactly at every original index.

If σ = 1, a qⁿ + b = Fₙ(b,θ). If σ = −1, then

a qⁿ + b = −Fₙ(−b,θ).

The negative branch reflects the center as well as the point.

Index the compact blockers by i = (K,k,N), with K ≥ 2, k ∈ ℤ, and N ∈ ℕ. This is a countable set. Choose positive budgets δᵢ whose sum is strictly less than ε/2; each is then less than 1. For each i take the proved blocker Hᵢ. Define

U = ⋃ᵢ (Hᵢ ∪ (−Hᵢ)).

Reflection preserves fundamental-interval density for one-periodic sets. The proof handles the change between [0,1) and (0,1] by their null endpoint difference. Countable subadditivity yields

D(U) ≤ ∑ᵢ [D(Hᵢ) + D(−Hᵢ)]
≤ 2∑ᵢ δᵢ < ε.

The union is open and one-periodic. Given arbitrary a,b,q,N, choose the index (K,k,N) provided by the exact parameter cover and use the appropriate sign. That member hits the requested original tail. No continuum parameter was reduced to a countable set: only the compact **ranges**, integer scales, and tail thresholds were exhausted. Every blocker still handles its full real parameter rectangle and all real centers.

Sources: `ContinuumGeometric/GeometricParameters.lean` (`geometric_parameter`, `dyadic_power_eq`); `ContinuumGeometric/GeometryChain.lean` (`exists_compact_exponent_range`); `ContinuumGeometric/CoefficientCover.lean` (`affine_geometric_compact_power_cover`); `ContinuumGeometric/CountableExhaustion.lean` (`unitDensity_reflectedSet`, `smallCompactBlockerSpec_open_exhaustion`).

## Compactification and the completed Lean chain

Take E = [0,1] ∖ U. It is a closed subset of the compact interval [0,1], hence compact. Since U is measurable and endpoints have measure zero,

λ([0,1] ∩ U) = D(U),
λ(E) + D(U) = 1.

The strict bound D(U) < ε therefore gives the strict requested inequality λ(E) > 1 − ε. Every tail point supplied in U is outside E. This proves all parts of `MainTarget` with the required order of quantifiers.

The final chain is:

```text
exists_routing_schedule
  + actual_stable_missed_center_probability_le
  + actual_routing_blocker_of_actual_stable_miss
  ⇒ smallCompactBlockerSpec_proved

smallCompactBlockerSpec_proved
  + smallCompactBlockerSpec_open_exhaustion
  + compact_complement_of_open_small
  ⇒ mainTarget_of_smallCompactBlockerSpec applied to the proved specification
  ⇒ geometric_main_target : MainTarget
```

Some preserved module comments use historical words such as `OPEN` or `UNRESOLVED` for proposition definitions or conditional intermediate lemmas. Those comments are not hypotheses of the final theorem. `MainProof.lean` explicitly supplies the construction and the stable probability bound needed by the conditional interfaces.

The accompanying verification materials report independent source/construction review, clean owned-source builds, exact-statement probes, and complete stored proof-closure replay in Lean. Mathematical exposition, finite regression tests, and kernel checking serve different purposes; finite checks do not replace the universal proof. The theorem continues to rely on Lean's foundational and implementation trust assumptions. This roadmap makes no novelty, priority, or external professional-human peer-review claim.
