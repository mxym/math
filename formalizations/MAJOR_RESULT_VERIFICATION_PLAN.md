# Complete formal verification of major results

The owner requested on 8 October 2026 that especially significant
results with no identified written-proof gap subsequently receive
complete Lean formalization. This document states what completion must
mean; it does not certify any new endpoint.

## Acceptance boundary

A complete formalization must prove the actual published theorem with
its original definitions, parameter range, boundary cases and equality
statement. A formally checked scalar inequality, conditional compactness
argument, or model calculation is a partial result. Neither a green build
nor a large number of checked declarations promotes it to the full
mathematical theorem.

No missing analytic or geometric bridge may be replaced by a custom
axiom, `sorry`, or a premise equivalent to the desired conclusion.
Established mathematical inputs that are not themselves formalized
must be listed as explicit external dependencies; an endpoint conditional
on those inputs must be labelled conditional. A fully formal theorem
requires their proved Lean counterparts as well.

The checked statement and its dependency report must be independently
read. Official compiler and library versions must be pinned; source
compilation, admitted-axiom checks, and kernel replay must use the actual
frozen public source. Negative controls should target material omitted
hypotheses. Existing immutable releases retain their original verification
scope; a later complete formalization receives a separate version.

## Priority: complete Gaussian first-moment results

The published all-k equal-mass theorem and its prescribed-mass centroid
ellipsoid extension currently have complete written proofs and **partial**
Lean checks. Their public status must continue to say that the full
Gaussian endpoints are not formalized.

The full all-k target must use actual standard Gaussian measure, measurable
or fractional partitions of mass 1/k, Bochner first moments, and the
coefficient (E max of k independent standard normals)^2/(k-1). It must
also prove the regular-simplex equality characterization when dimension
is at least k-1, and the stated strictness below that dimension. An
abstract covariance functional with its principal properties assumed
is not the same target.

The dependency order is:

1. Define the precise Gaussian partition/moment objectives and prove the
   required integrability, null-set invariance and finite-dimensional
   reductions.
2. Prove the covariance/price dual construction, including degenerate
   covariances, continuity and homogeneity.
3. Prove balancing-price regularity, interface flux, and the derivative
   identities used to instantiate the existing radial comparison.
4. Supply a proved formal counterpart of the imported Milman--Neeman
   multi-bubble perimeter theorem, or explicitly retain that theorem as
   an external input and label the resulting formal endpoint conditional.
5. Instantiate the already checked scalar comparison and prove the actual
   moment inequality, rigidity and dimensional boundary cases.
6. For the prescribed-mass extension, additionally prove the model
   interface Laplacian, profile Hessian/pseudoinverse identities and
   translated-simplex equality cases.

These are substantial missing mathematical developments, not completed
checks. This plan makes no date or effort estimate. Existing written
publication is distinct from completion of this formal verification.

## Selecting future conjectures

Before a new major proof is scheduled for full formalization, verify
whether the exact endpoint already has a public proof or disproof,
including web-hosted manuscripts. The Foregger prior-collision record
in `research/novelty-assessment/2026-10-08-foregger-power-prior-collision.md`
explains why that candidate is not currently scheduled as a new original
conjecture breakthrough.

## Completed: universal finite-group orbital primal-dual theorem

The [complete package](orbital-primal-dual/README.md) formalizes Theorem 18
of `notes/sharp-robust-permanent/paper.md`, with the original actual
probability, image-marginal, TV, kernel-supremum, orbital and conjugacy-class
objects. It includes real optimality, rational primal/dual certificates,
the actual linear-span formulation, all atoms and sharp disjoint
perturbations. Missing real-duality and rationality bridges were proved
rather than imported as assumptions. The verified record contains 117 owned
theorems, 28,264 declarations replayed from an empty kernel at trust level
zero, three positive controls and one rejected omitted-mass control.
Internal independent AI semantic reviews cover both the rational bridge
and the final correspondence with the original theorem.

This completion does not certify the note's separate closed formulas in
Theorems 15–17, every theorem elsewhere in the repository, or the Gaussian
analytic endpoints above. It is a full verification contribution for this
existing theorem, not a new conjecture solution.

## Further actual bridges now under development

The [actual Gaussian optimization package](gaussian-measure-primal-dual/README.md)
now proves price minimizer existence, balancing cells, uniqueness up to a
common shift, attained primal-dual equality and almost-everywhere fractional
rigidity using the actual `stdGaussian` measure and Bochner moments. Its
nine frozen mathematical modules and all 50 roots passed an empty-kernel
replay of 52,742 declarations at trust level zero. A second fresh compilation
and replay passed through the portable runner's unchanged proof-checking
body; its final strengthened toolchain preflight was tested separately and
the recorded scope explicitly distinguishes these executions. An
[independent internal semantic review](reviews/gaussian-measure-primal-dual-2026-10-08.md)
checks the actual definitions and endpoint assumptions.

The imported multi-bubble theorem and subsequent
analytic/equality chain remain necessary dependencies of a fully formal
Gaussian endpoint; they are not discharged by scalar or measure-foundation
checks.

The parallel [complete complex-Hermitian Bapat formalization](bapat-q-permanent-counterexample/README.md)
now proves the original-interval existential order-200 counterexample.
Its recorded verification covers all 22 source modules and 928 owned
declarations, with a 22,371-declaration empty-kernel replay. The actual
Gram/Fischer correspondence, ordered recurrence and all 200 arithmetic
transitions are included. Its positive diagonal shift and interior
decrease points are existential real numbers, rather than the paper's
specified rational epsilon and q0. The root task inspected its actual
final statements and recorded scope; this is a parallel contribution.

The separate
[actual endpoint and perturbation package](bapat-q-permanent-dependencies/README.md)
proves the universal deleted-minor identities, Hermitian real-value
correspondence, exact inversion bound, positive-definite perturbation,
non-diagonality, and an explicit violation on the original interval from
an actual negative-endpoint Gram input. The complete fresh-source record
checks 52 owned theorems and replays 21,571 declarations from an empty kernel,
with three positive controls and one rejected omitted-derivative control.

The separate [complete specified-rational proof](bapat-q-permanent-explicit-rational/README.md)
now supplies that actual definition and input correspondence and proves the
paper's specified dimension-200 complex Hermitian witness unconditionally.
It includes rational entry formulas, the exact rational epsilon and q0,
positive definiteness and the strict reversal on the original interval.
Its six mathematical modules, 30 theorem roots and 22,812 dependency declarations
passed a fresh source compilation, complete empty-kernel replay and false-data
control. A separate 928-owned-declaration, 22,371-declaration continuation
rechecked the completed fresh original source build after the earlier
reproducer's timeout; the failed earlier record is retained as FAILED.
The complete 52-theorem input run was reused and explicitly recorded.

The separate real-symmetric existence chain is now closed in the
[complete public package](bapat-real-symmetric-existence-counterexample/README.md).
`BapatRealExistence.exists_integer_real_symmetric_counterexample` proves the
finite integer positive-definite counterexample without a negative-input
premise. Its recorded independent run compiled 67 modules and replayed the
54,739-declaration closure into an empty kernel. It supplies no explicit
matrix dimension or dimension bound. This later completion does not change
the narrower scope of the earlier transfer theorem or its historical audit.

## Publication inventory after the all-cycle completion

The [October 2026 preprint collection](../preprints/lean-certified-2026-10/README.md)
maps each printable principal theorem to its actual complete Lean endpoint,
records manuscript-only ancillary statements separately, and preserves the
fixed formal source snapshot. It includes cycle classification, sharp simplex
stability and exponent sharpness, all-quadratic-order moats, robust continuum
avoidance, finite-action orbital primal/dual theory, and three exact
conjecture-counterexample papers. The already published combined Bapat paper
is indexed separately. Gaussian geometric endpoints and arbitrary-graph
Chollet remain outside the complete-main inventory.

The later [Wakhare four-root Lake project](wakhare-entropy-four-roots-lean/README.md)
also closes the actual `ℝ[X]` endpoint directly from the original binomial sums.
Its [CI run 37853632676](https://github.com/mxym/math/actions/runs/37853632676)
passed at commit `93a7512b3606581fcbbca310c7d2d587a8c1a903`: 1,643 Lake tasks,
12 standard-axiom audits, source hashes and an invalid-proof rejection control.
The older entropy formalization already proves the original real-power bridge
and is retained in DOI `10.5281/zenodo.23249754`; that frozen archive does not
include the later five-module implementation. This is an additional complete
formalization, not a new discovery of the mathematical counterexample.
