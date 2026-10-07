# A logarithmic upper Banach density criterion for the Erdos similarity problem

**First public version:** v1.1, 2026-10-07. The version number records revision of a private draft, not an earlier public disclosure.

**Attribution:** mxym (repository account), prepared with AI assistance. No institutional affiliation, independent referee review, or proof-assistant verification is asserted.

## Result and scope

A positive logarithmic upper Banach density criterion for nonuniversality; infinitely many points outside the avoiding set in every nontrivial affine copy; countable simultaneous avoidance; and effective certificate search for computably enumerable rational configurations. The squarefree-indexed dyadic sequence is an explicit application. This does not settle arbitrary infinite configurations.

The [complete LaTeX source](v1.1/build/main.tex) contains every proof and reference. No proof depends on a private transcript. See the [proof audit](v1.1/PROOF_AUDIT.md) for dependencies and limitations. The build produces `v1.1/paper.pdf`.

## Build and replay

From `v1.1/`:

```sh
(cd build && pdflatex -interaction=nonstopmode -halt-on-error main.tex && pdflatex -interaction=nonstopmode -halt-on-error main.tex)
cp build/main.pdf paper.pdf
python3 verification/check_cover.py --self-test
python3 verification/check_cover.py verification/toy_certificate.json
```

LaTeX packages: amsmath, amsthm, lmodern, microtype, geometry, hyperref and enumitem. The verifier uses standard-library Python integer and rational arithmetic only. Its six regression cases include endpoint-only failures and a true toy cover of density 9/10. **That toy is not a small-density certificate for the full theorem.** The existence theorem and countable-scale passage are written proofs, not machine-formalized assertions.

## Provenance and citation

The routing and exceptional-center repair methods are adapted from OpenAI, *The geometric case of the Erdos similarity conjecture*, October 5, 2026, family 084, pinned snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The source rederives the required arguments and identifies the proposed extensions. Upstream rights and notices remain applicable; see the root NOTICE and retained Apache-2.0 license.

```bibtex
@misc{mxym2026logdensity,
  author = {mxym},
  title = {A logarithmic upper Banach density criterion for the Erdos similarity problem},
  year = {2026},
  note = {Research manuscript, version 1.1; AI-assisted; not peer reviewed},
  howpublished = {\url{https://github.com/mxym/math/tree/main/preprints/004-log-density-similarity}}
}
```

Replace `main` by the exact publication commit for reproducible citation. Public disclosure does not certify first discovery. Literature-priority comparison remains separate.
