# Final copy consistency review of the transport series

Date: 8 October 2026.

## Decision

**FINAL COPY PASS.** The three typeset papers faithfully preserve the reviewed mathematical results and their necessary qualifications. No missing hypothesis, changed exponent, reversed inequality, omitted repair, or inflated verification/priority claim was identified in the reader editions. No manuscript correction is required by this limited review.

This decision concerns consistency of the final TeX/PDF copies with the already reviewed source snapshots. It is not a new research audit, an audit of the proof of (P), formal verification, historical-priority certification, or authorization to publish.

## Exact copy under review

Directory: `research_math/transport_series_manuscripts_20261008/`.

Archive: `transport-stability-series-20261008.tar.gz`.

Archive SHA-256:

    6a6458cd4c5546e7254a9e772eaf4d0e39450c6ab46d59721073f294432a151f

The publication manifest contains exactly 33 unique files. Every listed payload hash was checked; all 32 entries in `SHA256SUMS` passed. All 33 archive files were compared directly with their corresponding current candidate files and matched byte-for-byte. The preserved mathematical sources match the reviewed hashes:

- Top-N: `c3cf5061de5ac9298f3fb88e07800c9d88257b01a1cd80f82fdc5e1a083055c1`.
- Binary mass: `6858879d5acb26657b7d83ffc1b99386e67cd5c9fbf60ab451b579d132f1b9d8`.
- General moment after repair: `2e683e3cf79a373e6f7921bf2d25e45783484548cb7abf85c765a0486f46efbe`.

The obsolete pre-repair third source and its original open-gap verdict are clearly marked as historical provenance. The final limited recheck is correctly identified as superseding that status.

## Content checked

I read the complete three TeX proof bodies and their front matter, comparing their formulas, theorem conditions, and proof structure against the reviewed source snapshots. I also inspected the source map, review-status text, manifest, build/reproduction records, and extracted PDF text. Lightweight integrity checks were rerun independently. The retained section counts are 12, 9, and 9; all 99 original display tags are present in the TeX and rendered PDF text. Named internal references and citations resolve to defined targets.

### Top-N paper

The reader edition preserves d>=2, p>2, s=p/(p-2), beta=s-1, both slow-variation derivative assumptions, the fixed source, unrestricted target positions/masses, the p-moment budget, and the simultaneous quantifiers N>=3 and 0<w<=w_0. The N=1 exact formula and the restricted N=2 addition remain qualified correctly.

The top-N sum, implicit K_N(w), adjacent-scale inequalities, finite-step Holder exponents, potential-to-gradient estimate, exact two-endpoint matching, selected-scale moment normalization, and full 2M+1 atom count are retained without sign or exponent changes. The logarithmic cases, fixed-N criterion, and oscillating-L example agree with the reviewed source. Genuine ratio-one CDF asymptotics use `sim`; comparison formulas use `asymp`.

(P) is displayed explicitly. The abstract, body, and series README retain the conditional nature of the upper and two-sided statements, identify manuscript 001 v3 Theorem 1.1 and its permitted extended-support class, and expressly state that the upstream proof was not audited here. The lower construction remains independent of (P). The clarification restricting V's cell-activity description to the source's transverse support is present.

### Binary-mass paper

The reader edition preserves the independent exponent alpha=beta+1>1, d>=2, p>2, the fixed source, and the distinction among unrestricted binary masses, a minimum positive mass eta, and exactly the same prescribed mass vector for both targets. Dirac/coincident-label conventions and simultaneous small-w/mass constants remain intact.

The fixed-mass formula retains the additive w term and the correct minimum; the other formulas retain the running maximum with max(h_w,q(eta)). The all-directions halfspace estimate is still proved in Section 2.3, equation (2.5). The weighted divergence sign, mass-preserving rotation velocity, centered 2x2 cost, acute decomposition, obtuse relabeling, and exact-mass hinge formulas retain their reviewed signs and factors.

The alpha=2s threshold, negative logarithmic corrections, all-real-gamma qualification, and minimum-weight crossover retain their exact exponents. The paper continues to disclaim dependence on (P) or the top-N theorem.

### General-moment paper

The expanded source and target definitions agree with the fixed definitions imported from the second paper; they do not enlarge the theorem's scope. All of (M) is displayed, including convexity, strict increase, normalization, and monotonicity of Phi(r)/r^2. R is defined on (0,1] and E on (0,1/2]. The response function, three envelopes, exact scalar maximum, continuity iff statement, and bounded-radius specialization agree with the repaired source.

The third paper explicitly imports the second paper's Section 2.3, equation (2.5), and identifies its Section 3 coupling calculation. The cited section and equation actually exist under those numbers. The abstract and README do not present the three papers as logically independent, and no use of (P) has been introduced.

Both endpoint repairs are retained in full. Section 7.1 compares against t^-1 log(e/t)^(-gamma/2), takes its running maximum, and uses the exact scalar inverse without claiming a derivative limit for Phi or E. Section 7.2 uses the explicit t^(A-1)log(e/t)^b model and preserves all three A<1, A=1, A>1 cases. The derivative signs, inverse logarithmic powers, and max(gamma+2/q,0)/4 boundary exponent are correct. No added C^1, regular-variation, doubling, or logarithmic-derivative assumption appears in these applications. Section 6's extra derivative assumptions remain confined to that separate index principle.

## PDF and layout checks

Current PDF hashes and page counts:

- `top-n/main.pdf`: 12 pages; SHA-256 `026835142ba5402df4ecd20f8f1b085f2843fd18520e701558066441bb9f3241`.
- `binary-mass/main.pdf`: 11 pages; SHA-256 `ea26a1d600998a8d35892704239a0409639c504e9cd64e5ed06031d150490548`.
- `general-moment/main.pdf`: 9 pages; SHA-256 `98b0563da4a8a1b21b06f003655481b5591b32f2f5b167fd79f183fea14e5571`.

Extracted text hashes match the recorded integrity report. No replacement-character or unresolved-reference markers were found by the lightweight check. Available build diagnostics pass that check.

For independent targeted visual confirmation, I freshly rendered and inspected top-N pages 2-3, binary-mass pages 2-3, and general-moment pages 2, 7-8 from these exact PDFs. These cover the principal theorem displays, (P), (M), and both repaired endpoint arguments. Formulas, inequality signs, powers, delimiters, equation tags, and page-boundary placement are readable, with no clipping or collisions on the inspected pages.

The author's full-page visual inspection and clean byte-identical rebuild are recorded in the supplied QA/reproduction documents. I did not repeat the complete 32-page visual pass or rebuild the TeX during this limited review. The fresh targeted renders are only temporary inspection files and are not part of the publication candidate.

## Public status and final dependency verdicts

The front matter and README accurately call the records AI-assisted analytic checks. They explicitly distinguish them from Lean/other formal verification, professional certification, external peer review, and historical-priority certification. The papers attribute the antecedent mechanisms and do not claim historical firstness. The package says publication is a separate authorized step.

The mathematical statuses remain:

- Top-N: conditional PASS on imported (P).
- Binary mass/phase: PASS.
- General moment, including repaired endpoints: PASS.

No publication, external upload, large build, manuscript edit, or archive repack was performed during this copy review. The exact 33-file candidate and archive hash above remain unchanged. This receipt is stored outside that candidate so it does not silently change the approved manifest or archive.
