# All-real Jacobians and exact response fibers of finite tree compartment models

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536.

[Prepared PDF](paper.pdf) · [Editable LaTeX](paper.tex) ·
[Theorem–lemma–Lean correspondence](THEOREM_MAP.md) ·
[Source-bound internal manuscript review](MANUSCRIPT_REVIEW.json) ·
[Literature comparison](LITERATURE_UPDATE.md) ·
[Preparation and layout evidence](PREPARATION.json) · [Source bundle](paper-source.zip).

This 9-page manuscript organizes the already established finite-tree theorem
family into a focused paper. The all-real arbitrary-leak Jacobian, exact
coordinate powers and zero set, and complete real full-positive-target fibers
are proved on the actual compartment matrix and original principal diagonals.
For a prescribed leak the exact count is `(N-1)! / product_(v != o) |T_v|`;
an unknown single leak site gives N times that many distinct matrices. The
paper includes full ordinary proofs, including the general signed supported-
matrix diagonal gauge and same-site conservation rigidity needed before
positive leak relocation can classify an unrestricted real competitor.

The root-leak specializations mathematically imply Gross–Meshkat–Shiu
Conjectures 5.5 and 5.9. Those original statements and author attributions
are preserved. Classical tree enumeration and the star/path counts are
prior art; this paper does not certify first historical discovery.
The 1979 author-repository abstract was obtained; that full article was not.

The main statements map to the existing fixed Lean package at
`c2a2ce36ea6c5e000225574835f5a3ceddc748b4`. Its original independent
[run 38383557356](https://github.com/mxym/math/actions/runs/38383557356)
records 220 owned modules, 1,677 roots, 53,370 used declarations, trust-level
zero empty-kernel replay, only the standard three axioms, and rejection of
91 deliberately false source mutations. Those numbers count package modules,
roots and dependency declarations, not new mathematical discoveries.

On 2026-10-14 this preparation round independently compared all 235 proof,
reproduction and public-scope inputs to the current tree, original commit
and verified-source archive; all matched. It also matched the original ZIP
digest with the GitHub API artifact and confirmed the successful job.
The [readback evidence](../../verification/research-resume-20261014/README.md)
is a source/archive/API check, not a new Lean build or audit. No owned proof,
scope input, module, root or trust assumption was changed or added.
The mathematical manuscript review is internal assistant review, not
external human peer review; the new prose is not certified merely by an old
kernel log.

The fiber theorem assumes a fixed finite labelled bidirected tree, one leak,
collocated input/state output and N distinct positive poles with positive
weights summing to one. All-real Jacobian theorems have no positivity premise.
No complex-rate/fewer-mode enumeration, general cyclic or multi-leak model,
off-diagonal output, unknown-topology count, noise theorem, nonlinear hydrology
or rainfall-only arbitrary controllability is asserted. Signed-control and
collocated-discharge theorems already in the broader package remain separate.

## Rebuild and provenance

```bash
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The PDF was rendered with Poppler and all nine pages inspected. Long-path
overflows were corrected and the final build has no overfull box or unresolved
reference. The standalone source ZIP contains the manuscript, theorem map,
review, preparation evidence, the original verified-source archive and receipt,
and the original Actions evidence ZIP. It contains no credential, handoff file,
agent trace, exploration cache or Gaussian worktree content. Dependency source
pins and reproduction instructions are in the preserved proof package; the
bundle does not claim to vendor every external dependency.

Status: prepared repository manuscript, not an aiXiv submission, new GitHub
Release or DOI. Original materials retain all rights reserved. If a publication
platform cannot preserve this authorization, no silent CC fallback is allowed.
OpenAI AI assistants assisted research, formalization, writing and review;
no external funding. Existing and third-party notices remain in force.
