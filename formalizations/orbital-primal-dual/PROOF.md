# Complete proof and correspondence with Theorem 18

This package formalizes §18 of
[the sharp robust permanent note](../../notes/sharp-robust-permanent/paper.md).
It does not formalize that note's separate explicit formulas in §§15–17,
or the Gaussian results in other directories. The mathematical statement
here is an existing repository theorem. Completing its formal proof is a
verification contribution, not a newly solved famous conjecture.

## Actual objects and the sharp constant

For finite nonempty `I`, a probability law is a real function `p` with
`p_i >= 0` for every i and `sum_i p_i = 1`. A finite feature matrix A has
no positivity or rank assumption. Matching means
`sum_i A_ji p_i = sum_i A_ji q_i` for every j. The signed kernel consists
of v with zero total mass and `sum_i A_ji v_i = 0`. Total variation is
`TV(v) = sum_i |v_i| / 2`.

`sharpConstant A i` is the supremum of the actual ratios
`|v_i| / TV(v)` over nonzero kernel vectors, with zero inserted in the
set. This convention gives zero for a trivial kernel and also when all
kernel vectors vanish at the distinguished coordinate. No optimizer is
an input to the final theorem.

## Probabilities, Jordan decomposition, and attainment

The positive and negative parts of a zero-mass v each have mass TV(v).
If v is nonzero, dividing those parts by TV(v) gives probability laws
P,Q with matching features, disjoint supports and TV(P-Q)=1. Conversely,
P-Q belongs to the signed kernel for any matched pair, and TV(P-Q)<=1.
These facts prove equivalence of the signed bound and the bound
`P_i-Q_i <= C` over actual probability pairs, for C>=0.

The feasible probability pairs form a closed subset of the compact cube
`[0,1]^I × [0,1]^I`. They contain the uniform pair. The continuous
objective attains a maximum C, and `0 <= C <= 1`. If C>0, an optimal
pair must have TV(P-Q)=1: otherwise its normalized Jordan parts give a
strictly larger objective. Since `sum(P+Q)=2`, equality in
`sum |P-Q| <= 2` forces P,Q to have disjoint supports.

The original response around uniform measure is also proved. For every
kernel v, sufficiently small positive epsilon makes `u+epsilon v` a
nonnegative probability law with matching features. Thus a response
bound for all actual probability laws around u implies the signed
bound. Conversely, subtracting u from such a probability law produces
an actual kernel vector. This is an equivalence, rather than an assumed
local optimization principle.

## Constructed real duality

Give the signed-function space the l1 norm. The distinguished-coordinate
functional on the actual constraint kernel has norm C/2. One inequality
follows from the signed bound; the reverse inequality follows from
minimality of C. Lean proves both directions.

The real Hahn–Banach theorem extends this functional to an l1-space
functional g of the same norm. The functional `coordinate_i - g`
annihilates the kernel of the map consisting of the total-mass row and
all feature rows. Finite-dimensional linear algebra then represents it
as `c * total_mass + sum_j coeff_j * feature_j`. Evaluating on unit
coordinate vectors gives

`indicator_i(k) - sum_j coeff_j A_jk = c + g(e_k)`.

Consequently the score lies between `c-C/2` and `c+C/2`. Its oscillation
is at most C. Integrating any dual score against matched probability
laws shows that its oscillation bounds their objective; the attained
primal therefore makes this inequality an equality. This proves real
strong duality and constructs the dual optimizer. There is no imported
LP-strong-duality axiom or theorem-as-premise here; Hahn–Banach and its
used dependency closure are themselves checked in the kernel replay.

## Rational optimal witnesses without rounding

The package proves its own finite rational-projection lemma. For any
finite set s of real numbers, there is a rational-linear map
`f : R -> Q` that fixes 1 and preserves nonnegativity on s.
It is **not** required to preserve order on all of R.

To prove this, take the finite-dimensional rational span of s and 1,
and choose a finite rational basis. The inclusion of each basis vector
in R supplies a real coordinate vector. Every strictly positive element
of s, and 1, impose a strict linear inequality in these coordinates.
The original inclusion satisfies all those inequalities, so their
intersection is a nonempty open set. Density of rational vectors gives
rational coordinates in the same open set. The resulting rational
linear functional is positive on the specified positive inputs and on
1. Extend it linearly from that subspace to R and divide it by its
positive value at 1. Zero inputs map to zero. This proves the claimed
finite nonnegativity assertion.

For a rational feature matrix, apply the **same** f simultaneously to
all coordinates of a real optimal primal pair, the real dual
coefficients and endpoints, and all primal/dual inequality slacks.
Linearity preserves normalization, rational feature equalities, and
primal-objective equals dual-width. Finite sign preservation preserves
both nonnegative laws and every dual inequality. Thus the resulting
rational primal and rational dual have exactly zero gap.

The original real optimum bounds the rational primal from above. The
new rational dual bounds the original real optimum from above. These
two bounds prove that the rational value equals the original real
optimum. The bound still quantifies over **all real probability laws**,
not only rational laws. Empty feature index sets and zero slacks are
included in the proof.

## Group action, orbitals, and conjugacy classes

For a finite group G acting on finite Ω, the actual feature row indexed
by `(x,y)` is `1_{g • x = y}`. `imageMass` is its corresponding probability
sum. The generic matching definition is proved equivalent to equality
of all these actual one-point image marginals. Faithfulness and
transitivity are not assumed. Decidable equality on finite Ω is a Lean
presentation choice, not a mathematical restriction.

Orbitals are the actual quotient of Ω×Ω by the diagonal G-action.
`orbitalFeatures o g` counts x for which `(x,g • x)` belongs to orbital o.
Changing x by the bijection `x -> h • x` proves conjugacy invariance.

For a central law, its image marginal is constant on each orbital.
Expanding the expected orbital count gives the sum of those marginals
over the orbital. Since the orbital containing any specified `(x,y)`
is nonempty, its cardinality is positive. Equality of the orbital
moments therefore implies equality of each individual marginal.
The converse follows by summing. Both implications are formalized;
an orbital relaxation is not silently substituted for the original
constraints.

The group quotient uses actual `ConjClasses G`. `pushLaw` sums a law on
each class; `liftLaw` divides class mass by the actual class cardinality.
Every class has a representative, so these denominators are positive.
Pushing a lifted law recovers its class mass. Lifting a pushed central
law recovers the law. Both maps preserve probability normalization.
The identity class is exactly the singleton `{1}`, so its class mass
is precisely the identity atom.

`classFeaturesQ` is a rational-valued quotient lift of the integer
orbital counts. `class_matrix_is_average` proves that its real cast is
exactly the mean over each actual conjugacy class, as in equation (89),
including the class-size denominator. `class_lift_match` and
`central_class_match` prove the correspondence between the class LP and
actual group marginals. No alternate surrogate matrix is used.

Applying the proved rational primal-dual theorem to this class matrix
constructs rational optimal class laws and coefficients. Lifting the
laws gives central group laws with the same identity excess. Conversely,
every group-law pair matching the individual image marginals matches
the orbital moments, so the constructed orbital dual bounds its
objective. Hence the group optimum, class optimum and orbital dual
optimum are all the same rational number.

The class quotient is surjective. The actual dual maximum and minimum
on G therefore equal those on the class quotient.
`orbital_span_exact_minimum` additionally proves the original formulation
with the actual `Submodule.span` of the orbital count functions: finite
span membership supplies the coefficients, and the same oscillation
bound applies to every member of the span.

## Supremum, all atoms, equality interval, and controls

`sharpConstant_eq_optimum` connects the attained maximum back to the
actual signed-kernel supremum. It proves boundedness of the ratio set
and treats zero optimum separately. `sharpConstant_trivial_kernel`
checks the original zero-kernel convention.

Left translation permutes the individual marginal constraints and
preserves TV. `kernelRatios_all_atoms` proves equality of the actual
ratio sets at every atom; `sharpConstant_all_atoms` proves equality of
their suprema. The uniform-law bound holds at every atom, with the same
optimal constant. `sharp_attainment_all_atoms` supplies actual translated
kernel vectors and a full positive interval of sharp probability laws.

For a positive optimum, the central optimizing pair is disjoint. The
formal statement constructs epsilon>0 such that every delta in
`[0,epsilon]` gives the probability law `u+delta(P-Q)`, matching uniform
marginals, with TV exactly delta and identity excess exactly C*delta.
The endpoint delta=0 is included.

Three checked controls verify nonvacuity and a boundary condition: no
features on two atoms give C=1; a one-atom zero-mass kernel gives C=0;
and a vector of mass one has TV=1/2 and its proposed normalized Jordan
positive part has mass two. The separate negative-control file tries
to call that last function a probability law and must be rejected.

The source build, complete used-proof-closure replay from an empty
kernel at trust level zero, and axiom audit are distinct checks. Internal
AI-agent semantic review is additional scrutiny, not external human
peer review. Nothing in this package asserts that all other repository
research has received complete Lean formalization.
