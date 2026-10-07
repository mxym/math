# Mathematical audit record

Date: 7 October 2026.

Two separate independent model mathematical readings passed: one covered the
positive stability theorem and its constants, and the other covered the
all-class sharpness obstruction and product-recovery geometry. Neither found a
substantive mathematical gap. These are independent mathematical audits, not
human peer review or proof-assistant verification. No novelty or priority
conclusion is drawn.

The audited input was the complete English manuscript with SHA-256
`d6448a3f6e35ac999293de5585352c3b899029dd5fc3e3be19a347b4ca3fe9eb`.
The release article preserves its mathematical argument. It corrects a missing
backslash in `\quad`, explicitly records the already implied conditions
`M > 0`, `0 < a <= 1`, and full dimensionality in the relevant lemmas, and
revises presentation, bibliographic metadata, and literature comparison.
The hashes of the release files are recorded in `MANIFEST.json`.

## Positive theorem: scope of the passed audit

The audit checked the following analytical gates rather than inferring the
theorem from finite examples.

- The v2–v4 affine normalization, ordered determinant factorials, cone-law
  continuity passage, Rademacher equality branches, and full equality class
  agree with the primary source bytes recorded in `DEPENDENCIES.json`.
- The regular-contact identity `E[Y X^T] = I/d` and sequential wedge estimate
  give the lower bound on determinant mass for general symmetric bodies.
- The robust balanced-coefficient lemma retains the half-mass equality branch.
  The conditional contact-slab estimate cancels the determinant denominator
  before integration, including arbitrarily ill-conditioned conditioning
  matrices. The weighted layer-cake estimate includes singular tuples and zero
  deficit.
- Simultaneous control of the one-sample and all omitted-basis two-sample
  sections permits selection of one determinant-good basis. Exact omitted-basis
  cofactor identities control overlapping coordinate pairs and yield a matching.
  This argument uses Borel partitions and integrals, so it includes nonatomic
  laws without assigning positive mass to any individual sample.
- Product recovery uses support functions and the first mixed-volume formula.
  A symmetric homothetic cap converts relative missing volume to containment
  without an inradius loss or an inverse cone-volume uniqueness assumption.
- The small-deficit threshold, the global John bound, and every algebraic
  simplification leading to `C_d <= d^15` were checked for all `d >= 3`.

The contact argument includes flat facets: their cone-law atoms arise from
positive-area sets of regular primal contacts. The proof constructs one block
matching and one product; it requires no canonical or unique product
decomposition.

The audit also checked a scope guard. The uniform even law on
`+/-e_1, +/-e_2, +/-e_3, +/-(1,1,1)/3` has `A = 3/16`, `B = 3/8`, and zero
upper defect, but expected fourth absolute cofactor `1/32`. Thus the cone-specific
estimate cannot be extended to arbitrary even boundary laws. The release makes
no such extension. This guard was independently enumerated in the audit; its
audit enumeration source is not part of the shipped regression suite.

## Sharpness and geometry: scope of the passed audit

The separate audit checked the exact corner-truncation facet-volume and
determinant normalization, the leading `t^d` deficit, and the lower distance
bound against the entire affine product class. In particular, it checked
oblique projections, diagonal-width estimates, idempotent rounding to blocks
of dimension at most two, all allowed factor shapes, and passage to the
Banach–Mazur infimum without assuming that it is attained. It also checked the
orientation and volume of the symmetric cap in product recovery.

The obstruction excludes powers above `1/d`. It does not prove that `1/d` is
attainable. The proven exponent is `1/(6d)`, and the interval between these
values remains open.

The sharpness audit reported eight additional facet-minor cases and 168
sign-sum cases in dimensions 3–30. Their separate audit sources are not shipped
and those counts are not included in the reproducible release totals.

## Computation and packaging

The shipped exact suite contains 5,696 cases and is replayed in ordinary and
optimized Python, with byte-identical output. It checks finite coefficient,
cofactor, and facet-minor identities. It does not verify the area formula,
Fubini selection, mixed-volume inequalities, or the all-dimensional analytic
proof. Scope and commands are in `VERIFICATION.md`; reference output is in
`results/`.

The audits identified one reproducibility defect in the earlier aggregate
driver: it assumed an unshipped `repo/` directory and could write logs before
failing. The release fixes this with self-contained standalone replay,
explicit optional external dependency input, read-only hash preflight, and a
separate output directory. Extracted-archive and failure-path regressions are
recorded in `results/package-tests.json`. PDF visual inspection and clean
rebuild evidence are recorded separately in `PDF_QA.md` and `BUILD.md`.

Saroglou and Liu–Xiong–Yang full-text comparisons remain incomplete. Their
available primary records are described conservatively in `LITERATURE.md`;
neither is a proof dependency.
