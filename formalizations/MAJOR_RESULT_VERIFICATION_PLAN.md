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
