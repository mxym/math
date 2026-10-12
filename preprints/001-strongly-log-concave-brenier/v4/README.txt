Sharp Gaussian Brenier stability under logarithmic second moments
Research manuscript 001, version 4, 7 October 2026

Focused continuation
This is a focused continuation of manuscript 001. It develops the sharp
logarithmic-second-moment threshold and the critical finite-q constant. It uses
the exact all-P2 potential theorem from public version 3 as an explicit cited
input rather than repeating that version's cell-calculus proof.

Version 3 remains the full record of the broader earlier results, including
compact log-concave sources, hard-boundary tail estimates, curve lifting and
conditional-cell transport inequalities. Versions 1, 2 and 3 are preserved.
The logarithmic theorem here does not extend to arbitrary hard-boundary sources.

Public proof dependency
Title: Sharp Brenier stability under target moment bounds, v3.
Repository: mxym/math, research manuscript 001, 7 October 2026.
Commit: 5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3.
Full proof, Theorem 1.1:
https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf
Source:
https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex
The exact inherited hypotheses and conclusion are restated as Theorem 2.1.
The new proofs are complete relative to this publicly available proof input and standard
convex-analysis/optimal-transport facts. No hidden conjectural assumption is used.

Main results
- Under normalized E[(|Y|/M)^2 log(e+(|Y|/M)^2)^beta] <= 1, beta>0,
  the exact Gaussian exponent is min(1/3, beta/(beta+1)).
- The beta=1/2 transition has no additional logarithmic loss.
- For beta=0 there is no uniform modulus in d>=2.
- A full-support strongly convex C1,1 source extension has an explicit constant
  uniform under fixed dimension, curvature and gradient-Lipschitz parameters.
  Sharpness is for that source class, not every non-Gaussian member.
- In the homogeneous finite-q one-third estimate, the best Gaussian constant
  has exact order (q-2)^(-1/6) as q decreases to 2, in every fixed d>=2.
- In d=1 the map distance equals W2 and the normalized best finite-q constant is 1.

The new minimum-density lemma justifies signed subtraction with L2 gradients
alone and produces polynomial source weights. The logarithmic pairing permits
arbitrary dependence between transport values and source coordinates. Rare
rotated halfspaces and a bounded three-atom family give the matching obstructions.

Build and files
Run: sh build.sh
The script uses latexmk if present, otherwise pdflatex and bibtex. It performs no
network access or installation. A standard TeX Live/MiKTeX setup with Latin Modern,
AMS packages, geometry, microtype, hyperref, cleveref and fancyhdr is sufficient.

manuscript.tex and references.bib are the editable sources; manuscript.bbl is the
generated bibliography; manuscript.pdf is the rendered result. CHANGELOG.txt,
BUILD_INFO.txt, QA.txt and SHA256SUMS document the snapshot. The source archive
contains all local typesetting inputs and the build script.

Status
Research draft, not formally verified or externally peer reviewed. No priority
or journal-quality claim is made. Qualitative uniform continuity under uniform
second-moment integrability is not presented as new. The comparison with Merigot's
HAL preprint hal-05616391 remains unfinished. The author field is blank.
