# Exact qutrit-qudit APPT purity: preprint

**Public preprint. Not peer reviewed.** This manuscript proves the exact maximum
for every n >= 3, including real quantum-state semantics and actual attainment.
Its main APPT theorem is completely Lean-certified in the separate immutable
[`appt-qutrit-purity-complete-v1`](https://github.com/mxym/math/releases/tag/appt-qutrit-purity-complete-v1)
proof release at commit `2fc3f25179cf1128c4bccbde65fd3a07c093ad6d`.

Read [the manuscript](main.pdf) or its [LaTeX source](main.tex).
The paper identifies the result as a proof of the qutrit maximal-value/attainment
part of Ahiable-Kothakonda-Winter Conjecture 6.7, not a new prediction of the value.
It distinguishes the earlier Dung-Khoi formula and Tran's prior disproof.

## Additional analytic consequence

Section 7 also derives the same exact purity maximum for absolutely separable
states. The large witness uses the spectral-ratio separability criterion in
Kondra et al., arXiv:2605.29197v1, Supplemental Lemma 2. The small witness is
proved separable by an explicit finite average of product projectors.
**This corollary is not Lean-formalized in the frozen APPT release.** Equal
maximal purities do not prove equality of the APPT and absolutely separable sets.

## Exact ancillary check

```sh
python3 ancillary/check_certificates.py --report verification/exact-checks.json
```

Only the Python standard library is needed. All seven certificate data files are
byte-identical to the frozen Lean package. The checker reconstructs every exact
polynomial identity, checks positive weights, rejects an intentionally corrupted
coefficient, and checks the phase-average coefficient identity for Schmidt ranks
1, 2, 3. No optimizer or floating-point calculation is used.

The fixed Lean proof remains separately reproducible with Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; its source and verification archives
are linked above. It passed 879 local modules, 18 verification stages, and a
155,787-declaration / 58-root initially empty kernel replay at trust level zero.
Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.

## Build the manuscript

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The release contains the PDF, LaTeX/ancillary source archive, and hash manifest.
It is posted as a versioned GitHub preprint. No arXiv submission or arXiv identifier
is claimed. The earlier proof and interim releases are immutable and unchanged.
The author's affiliation, funding statement, and AI-assistance disclosure are
included in the manuscript. No new blanket license is asserted for this deposit.
