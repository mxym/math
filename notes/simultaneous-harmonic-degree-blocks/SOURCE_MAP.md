# Source map and provenance

## Pinned upstream repository

- Repository: openai/math
- Commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
- Family: 361, *Failure of integer-degree harmonic dimension comparison*

Relevant public source files inspected:

- CONTENTS.md
- preprints/A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/introduction.tex
- preprints/A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/growth.tex
- preprints/A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026/build/sections/geometry.tex

The imported statement is the near-Euclidean corollary together with the
main theorem's harmonic-dimension lower bound. The present note does not
copy the upstream proof or claim to reprove its angular/radial construction.

## Deduction in this directory

The new mathematical step is to combine:

1. the upstream one-degree lower bound h_k >= c(k+1)^2, available for every
   fixed c < 9/4;
2. the elementary inclusion H_k contained in H_d for d >= k;
3. the integer endpoint inequality d+1 <= beta(k+1).

This yields a simultaneous interval of degree failures and its
two-parameter excess/block-length tradeoff.

## Licensing and claims

The OpenAI/math repository is publicly released under Apache-2.0; this
repository already carries its upstream license under
third_party_licenses/openai_math_LICENSE.txt.

No first-proof, novelty, or priority claim is made here. The note is a
newly recorded consequence relative to this repository's prior state, not
a literature-history assertion.
