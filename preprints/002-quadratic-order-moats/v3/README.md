# Bounded step walks on irreducibles in quadratic orders

Version 3, 7 October 2026. This is a 26-page English research proof draft with explicit attribution and verification caveats.

## Main files

- `quadratic_order_moat_v3.pdf`: rendered version 3 manuscript
- `source.tex`: self-contained LaTeX source with bibliography
- `CHANGELOG_v3.md`: mathematical changes from version 2
- `certificates_v3/`: separate exact checkers, complete positive and negative bundles, and independent reproduction scripts

A standard TeX Live installation can build the PDF by running `pdflatex source.tex` twice. No external figures or bibliography database are required.

Versions 1 and 2, including the old split-pair checker, remain preserved without modification. The main all-quadratic-order theorem and the A1–A5 analytic interface are unchanged. The inherited geometric and entropy argument remains prominently attributed to OpenAI's pinned Gaussian moat source, family 028.

## Version 3 result

Individual nonzero nonunit principal generators give exact periodic-sieve certificates, including ramified norm-prime elements and composite norms. Two adjugate congruences decide ideal membership; the least scalar period is the absolute norm divided by coefficient content. Verified quotient-component sizes and the selected set of norm values give stronger integer restoration bounds.

Complete four-step/eight-step examples give conservative full irreducible component bounds of 20/92820 for Z[i] and 179200/351232 for Z[sqrt(2)]. The proposed smaller Q30 Gaussian eight-step sieve is explicitly rejected by a nonzero-voltage walk; the Q130 certificate succeeds. No infinite irreducible walk is inferred from the failed candidate.

Computability is proved for integral order models with supplied finite coefficient-step sets. The bounded checkers do not implement the unrestricted terminating search, and the manuscript makes no practical-runtime claim or effectiveness claim for arbitrary noncomputable real metric inputs.

## Verification boundary

Every one of the 26 rendered pages was inspected. Double compilation has zero warnings, undefined references, missing-character errors, overfull/underfull boxes, or detected page-boundary overflow.

The 41 norm-prime tests and 24 general-principal tests pass. The separate finite-lift and direct multiplication-image reconstructions pass, as does the 184-generator arithmetic stress test. See `certificates_v3/README.md` for reproduction commands and explicit resource limits.

These are mathematical proofs with bounded exact computational checks, not Lean replay, external peer review, guaranteed publication priority, or optimal-bound certification. No authorship is assigned to a person by this draft.
