# A logarithmic upper Banach density criterion for the Erdos similarity problem

**Read:** [PDF](v1.1/paper.pdf) · [complete LaTeX source](v1.1/build/main.tex) · [proof audit](v1.1/PROOF_AUDIT.md) · [versioned release](https://github.com/mxym/math/releases/tag/density-simplex-20261007-v1.1)

**First public version:** v1.1, 2026-10-07. The version number records revision of a private draft, not an earlier public disclosure. First source commit: `e6c776cae39477baa4e1a03d59a1547417f1a68e`; compiled release snapshot: `e894ed8678052e45ecd9f1714b6a996cfea33cf3`.

**Attribution:** mxym (repository account), prepared with AI assistance. No institutional affiliation, independent referee review, or proof-assistant verification is asserted.

## Result and scope

A positive logarithmic upper Banach density criterion for nonuniversality; infinitely many points outside the avoiding set in every nontrivial affine copy; countable simultaneous avoidance; and effective certificate search for computably enumerable rational configurations. The squarefree-indexed dyadic sequence is an explicit application. This does not settle arbitrary infinite configurations. No proof depends on a private transcript.

An [additional model-conducted review](../../reviews/2026-10-07-independent-model-review.md) found no confirmed correctness defect and records [independent exact tests](../../verification/2026-10-07-independent-review/README.md). This is not human peer review or proof-assistant verification. The finite checker verifies supplied normalized covers, not the full infinite theorem or membership in a specified infinite configuration.

## Build and replay

From `v1.1/`:

```sh
(cd build && pdflatex -interaction=nonstopmode -halt-on-error main.tex && pdflatex -interaction=nonstopmode -halt-on-error main.tex)
cp build/main.pdf paper.pdf
python3 verification/check_cover.py --self-test
python3 verification/check_cover.py verification/toy_certificate.json
```

LaTeX packages: amsmath, amsthm, lmodern, microtype, geometry, hyperref and enumitem. The verifier uses standard-library Python integer and rational arithmetic only. Its [six recorded regression cases](v1.1/verification/self_test.json) include endpoint-only failures and a true toy cover of density 9/10. **That toy is not a small-density certificate for the full theorem.** The existence theorem and countable-scale passage are written proofs, not machine-formalized assertions.

## Provenance and citation

The routing and exceptional-center repair methods are adapted from OpenAI, *The geometric case of the Erdos similarity conjecture*, October 5, 2026, family 084, pinned snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The source rederives the required arguments and identifies the proposed extensions. Upstream rights and notices remain applicable; see the root NOTICE and retained Apache-2.0 license. A [post-publication comparison](../../comparisons/2026-10-07-density-simplex.md) records overlaps and limitations without asserting priority.

```bibtex
@misc{mxym2026logdensity,
  author = {mxym},
  title = {A logarithmic upper Banach density criterion for the Erdos similarity problem},
  year = {2026},
  note = {Research manuscript, version 1.1; AI-assisted; not peer reviewed},
  howpublished = {\url{https://github.com/mxym/math/tree/e894ed8678052e45ecd9f1714b6a996cfea33cf3/preprints/004-log-density-similarity}}
}
```

Public disclosure does not certify first discovery. Historical manifests should be checked at their fixed publication commit, because navigation files can subsequently evolve.
