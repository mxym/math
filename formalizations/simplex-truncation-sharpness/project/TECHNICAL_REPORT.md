# Technical report: actual entry005 truncation sharpness

The literal `Entry005.truncationSharpnessGoal` is proved by
`Entry005.truncationSharpness`. The exact geometric formula is a proved
lemma, not an assumption. The true maximum-inscribed relation compares every
actual inscribed Affine.Simplex. The excess uses that same simplex's original
centroid and the literal infimum definition. The original exponent and all
existential/universal target quantifiers are preserved.

## Inspected published material

The mxym/math paper and truncation source are pinned at commit
`3c6f6a1a53b0d524af50bd940c3f73f400b41516`. Source bytes, paths and hashes are
in `sources/provenance.json`. The relevant paper is
`notes/sharp-simplex-stability/proof.tex`, section Sharpness, equation
`eq:truncation`; the detailed calculation is
`notes/sharp-simplex-stability/sources/truncation/proof.tex`, theorem
`thm:exact` and corollary `cor:power`.

The complete inspected mxym tree contains 135 Lean files. Its primary Lean
project pins 4.34.1 and the same mathlib commit as this release. The relevant
published `lean/Entry005/Targets.lean` is byte-identical to this project's
Targets file, SHA-256
`8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`.
The public Entry005 directory contains definitions, cap/volume lemmas and
handoff interfaces, not a completed truncation sharpness proof. Its Mxym
modules include real finite Rademacher, equality, signed-square, determinant
and stochastic-rigidity material, inherited and rechecked here. No checkout
AGENTS.md or .agents skill instructions were found in that inspected tree.

OpenAI/math is inspected at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; it contains 117 actual .lean files,
with real ProjectionBody/SimplexVolume and ProjectionVolume/AffineBrightness,
AffineCovariance modules. The upstream project pins Lean 4.34.1 and the same
mathlib revision. Its build documentation recommends compiling small portions.
The chosen volume source prefix is copied unchanged: 6404 bytes, SHA-256
`1f46e7403100ac3275e390508fbcb43a84f0792fa493cb96dad2e41d5f4d713f`,
containing exactly eight reused public proofs. The complete relevant original
source and reuse provenance are delivered. Upstream support for other topics
does not certify the complete entry005 paper; only the selected, recompiled
and axiom-audited proof closure is claimed here.

## Exact closed statements

Let `d >= 3`, `0 < t < 1`, `q=t^(d-1)`, `c=1/(d-1)!` and
`K_t={x_i>=0, t<=sum x_i<=1}`. Several geometric lemmas hold in the larger
domains shown in their literal signatures, including the actual defect formula
for `d>=2`.

* `truncation_actual_volume`: actual Euclidean volume `(1-t^d)/d!`.
* `truncation_coordinate_facet_area`, `truncation_top_facet_area`,
  `truncation_bottom_facet_area`: actual intrinsic areas `c(1-q)`,
  `c sqrt(d)` and `c q sqrt(d)` respectively. They are derived through actual
  facet charts, explicit Euclidean isometries, radial Fubini and homothety.
* `truncation_actual_facet_vector` and `truncation_actual_facet_support`:
  raw actual data `(-c(1-q)e_i,0)`, `(c 1,c)`, `(-cq 1,-ct^d)`.
* `truncation_actual_projection_body`: the actual intersection-defined
  projection body equals the actual facet zonotope.
* `truncation_actual_projection_volume`: every true unit-direction actual
  projection volume is `c/2*((1-q)*sum |u_i|+(1+q)*|sum u_i|)`.
* `truncation_packed_horizontal_tuple_sum` and
  `truncation_packed_lifted_tuple_sum`: complete arbitrary-d ordered sums.
  Their factorial multiplicities come from finite injection enumeration and
  alternation. The all-coordinate, top, bottom and paired-special minors are
  all derived, including parallel cancellation.
* `truncation_entryDefect_exact`: the actual canonical geometric defect is

```
t^(d-1) [d(d-1)-(d+1)(d-2)t-2t^d]
/ [(d+1)(1-t^d)(d+1+(d-1)t^(d-1))].
```

  A proved actual interior translation makes every support positive before
  applying the finite cone-law/pyramid bridge. Actual intrinsic areas are
  translation invariant. A determinant-one row shear preserves lifted
  determinants. The original negative bottom support is never treated as a
  probability weight. Every denominator canceled in the scalar calculation
  is proved nonzero; no geometric equality premise remains.
* `truncationSimplex_maximumInscribed`: the chosen genuine simplex
  `S_t=conv(e_1,...,e_d,t e_i)` is globally maximum. Separate affine/convex
  determinant bounds extend actual polytope vertex bounds to arbitrary
  inscribed points, including face-interior vertices.
* `truncation_simplex_actual_volume`: its actual volume is `(1-t)/d!`.
* `truncation_simplex_centroid_containment_iff`: for every excess parameter
  epsilon>=0, actual `K_t` is contained in the actual original-centroid
  dilation iff `(d+1)t<=epsilon`.
* `truncation_simplex_excess_exact`: actual literal excess is `(d+1)t`.
* `truncation_entryDefect_pos` and `truncation_entryDefect_quotient_tendsto`:
  actual defect is positive and `e(K_t)/t^(d-1)` tends to the positive exact
  coefficient `d(d-1)/(d+1)^2` as t tends to zero from the right.
* `truncationSharpness`: for every d>=3, alpha>1/(d-1), C>=0 and epsilon>0,
  there is `0<t<min(epsilon,1)`, a genuine convex body with carrier K_t and
  nonempty interior, and a genuine globally maximum inscribed S, with
  `0<entryDefect K_t<epsilon` and
  `C*(entryDefect K_t)^alpha < excess K_t S`.

`coverage.json` is the complete 136-name map with actual compiled signatures
and all assumptions. The names above summarize the main mechanisms;
no extension beyond each formal type is claimed. Conditional assembly helpers
are also included with their displayed premises; the final target discharges
those premises using actual geometry.

## Verification and trust

All 125 mathematical modules, including all inherited source dependencies,
are compiled from source into a new empty owned output directory with the
pinned Lean kernel and autoImplicit=false. Every one of 850 public proofs has
explicit `#check` and `#print axioms` output. The separate environment audit
covers actual module ownership of private and generated declarations as well
as public proofs, using Lean's recursive axiom collector. Exact counts and
per-declaration closures are in `logs/truncation-verification.json`.

The only allowed logical axioms are propext, Classical.choice and Quot.sound;
individual proofs may use smaller subsets. No sorryAx, custom axiom, admit,
native_decide or skipped kernel checking is accepted. The imported closure
is checked before claiming the selected reuse certified. This audits the
selected imported facts, not every file of the entire OpenAI repository.
Mathlib is supplied by its official pinned cache, not rebuilt in full here.

The old mathematical sources are hash-verified unchanged. The older frozen
Library B bundle remains untouched. Managed network/runtime guidance was read;
normal inherited proxy and CA trust were preserved; official sources were used
without security bypass or introduced credentials.

## Explicit remaining coverage limits

There are no unformalized dependencies or assumed geometric identities in the
literal sharpness proof. The full prescribed stability upper-bound Main and
its exact dimension constants remain with the independent owner task.
This release does not formalize classification of all maximizing S_p,
arbitrary-p excess, the best-maximum infimum, Banach-Mazur bounds or the
Rogers-Shephard obstruction proposition. The traditional analytic proof in
SHARPNESS_PROOF.md discusses some of those extensions; that prose is not a
kernel certificate. No paper counterexample or inadequate assumption was found
for the sharpness target, and no exponent or target modification was needed.

No external push, PR merge or public publication occurred. This complete
source bundle and successful logs are intended for independent parent review.
