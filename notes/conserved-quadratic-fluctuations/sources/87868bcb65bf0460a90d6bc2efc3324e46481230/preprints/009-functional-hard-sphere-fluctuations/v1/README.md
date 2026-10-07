# Functional hard-sphere fluctuations on regular kinetic intervals

Research draft, version 1. 7 October 2026.

## Result

The paper proves weak convergence of exactly centered true and fixed pasted hard-sphere fluctuation fields in D([0,T], S′β(R⁶)), with the generalized J₁ topology induced by the strong dual of Schwartz space. The limit is a Radon Gaussian law supported on strongly continuous paths, throughout the prescribed regular Boltzmann interval.

The result uses the explicitly restated analytic history package and finite-dimensional Gaussian limit from the pinned upstream manuscript. The new cyclic-history estimate is √(ε[1 + log(1/ε)]), with a √ε bound in the repeated-pair sector. These are proof estimates; the paper does not assert a quantitative CLT rate or a rate of covariance convergence.

See `DEPENDENCIES.md` for the full imported/new proof boundary. `AUDIT.md` records the mathematical review scope, and `ARTIFACT_QA.md` records source and PDF checks. This remains a research draft; external peer review and a comprehensive publication-priority review have not been completed.

## Files

- `manuscript.pdf`: the complete 19-page paper.
- `manuscript.tex` and `sections/01_model.tex` through `sections/08_tempered.tex`: complete editable source.
- `build.sh`: portable build entry point for TeX Live installations.
- `source.tar.gz`: source-only archive with a separate internal checksum inventory.
- `SHA256SUMS`: checksums for the release files, excluding itself.

There are no external figure assets, bibliography databases, or private research-note build inputs. References are embedded in `manuscript.tex`.

## Build and verify

Requirements: a POSIX shell, TeX Live with pdfTeX, and `latexmk`. The required LaTeX packages are article, fontenc, Latin Modern, geometry, AMS math/theorem/symbol packages, mathtools, microtype, enumitem, aliascnt, needspace, hyperref, url, and cleveref. A standard full TeX Live installation supplies them. The script also handles a common Linux installation layout whose TeX tree and format cache are not on their default paths.

From the release directory:

```sh
sha256sum -c SHA256SUMS
sh build.sh
```

On macOS, `shasum -a 256 -c SHA256SUMS` can replace the first command. The build runs pdfLaTeX through latexmk until cross-references stabilize. No BibTeX invocation or network connection is needed.

For a clean build from the source archive:

```sh
mkdir clean-build
tar -xzf source.tar.gz -C clean-build
cd clean-build/functional-hard-sphere-fluctuations-v1
sha256sum -c SOURCE_SHA256SUMS
sh build.sh
```

PDF date and trailer metadata are suppressed. Byte-for-byte reproducibility was verified with the recorded TeX environment; other TeX/font versions may produce different PDF bytes while preserving the content. Never treat a byte mismatch across toolchain versions as evidence of a mathematical change without inspecting the source.

## Pinned upstream source

OpenAI, *Hard-sphere fluctuations on the regular Boltzmann lifespan* (23 September 2026), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:

https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build

Section 2 states the imported bounds and lists exact source labels. The new Gaussian geometry, calendar localization, and strong-path topology arguments are proved within the paper.
