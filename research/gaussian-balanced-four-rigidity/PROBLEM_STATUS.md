# Exact problem status checked before further research

Checked 8 October 2026. The active target is the maximum of
$\sum_{i=1}^4\|\int_{C_i}x\,d\gamma_d\|^2$ with all four masses exactly
$1/4$, in dimension $d\ge3$, and the proposed global regular-tetrahedral
classification. This is a fixed-mass first-moment problem.

Primary statements checked:

- Heilman, arXiv:1211.7138v2, Conjecture 3, conjectures origin conicity for
  the four-cell equal-mass problem in dimension three. It says simplicial
  conical; it does not itself say regular tetrahedral. The exact version
  and its PDF hash are recorded in SOURCES.json.
- Heilman, arXiv:1901.03934v1, Section 1.4, Problem 1.15 and Conjecture
  1.16, records the prescribed-mass first-moment problem for more than
  three cells. Its arbitrary-mass regular-simplex statement has the
  companion counterexample in this repository. That counterexample
  specifically excludes the equal-mass parameter and does not settle
  the active target here.
- Sun–Hu–Lan, arXiv:2008.04827v2, and Mulgund, arXiv:2609.28452v2,
  address centered unit-coordinate-variance Gaussian maxima. They do
  not impose prescribed label probabilities or permit the balancing
  prices in our objective. Their results cannot be treated as a solution
  of the active target without an additional proved reduction.
- `openai/math` was inspected at commit
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its *The Gaussian propeller
  bound in every dimension* (24 September 2026), introduction and main
  theorem, explicitly allows unrestricted cell probabilities and empty
  cells. Its three-sector extremizer is not a four-quarter partition.
  The source scan did not identify an equal-mass four-cell resolution.

The finite primary-source and follow-up literature scan did not identify
a later proof or counterexample for this exact equal-mass problem. This
is a limited literature screen, not a proof that no such paper exists.
The current research remains justified by the precise unresolved scope
in the sources checked. Any later matching resolution should trigger a
scope reassessment before more proof search or publication claims.

Status screening is done before starting a fresh target. A problem already
proved or disproved is not an active conjecture-solving direction merely
because its result has a short independent reconstruction. In particular,
the separately rediscovered complex Drury permanent counterexample was
removed from the active agenda after identifying Hutchinson's 2017
counterexample. No breakthrough release is warranted for that rediscovery.
